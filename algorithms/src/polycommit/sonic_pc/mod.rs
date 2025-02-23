// Copyright (C) 2019-2022 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use crate::{
    fft::DensePolynomial,
    polycommit::{kzg10, optional_rng::OptionalRng, PCError},
    snark::marlin::{params::OptimizationType, FiatShamirRng},
};
use hashbrown::HashMap;
use itertools::Itertools;
use snarkvm_curves::traits::{AffineCurve, PairingCurve, PairingEngine, ProjectiveCurve};
use snarkvm_fields::{One, Zero};

use core::{
    convert::TryInto,
    marker::PhantomData,
    ops::Mul,
    sync::atomic::{AtomicBool, Ordering},
};
use rand_core::{RngCore, SeedableRng};
use std::collections::{BTreeMap, BTreeSet};

mod data_structures;
pub use data_structures::*;

mod polynomial;
pub use polynomial::*;

/// Polynomial commitment based on [\[KZG10\]][kzg], with degree enforcement and
/// batching taken from [[MBKM19, “Sonic”]][sonic] (more precisely, their
/// counterparts in [[Gabizon19, “AuroraLight”]][al] that avoid negative G1 powers).
/// The (optional) hiding property of the commitment scheme follows the approach
/// described in [[CHMMVW20, “Marlin”]][marlin].
///
/// [kzg]: http://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf
/// [sonic]: https://eprint.iacr.org/2019/099
/// [al]: https://eprint.iacr.org/2019/601
/// [marlin]: https://eprint.iacr.org/2019/1047
#[derive(Clone, Debug)]
pub struct SonicKZG10<E: PairingEngine, S: FiatShamirRng<E::Fr, E::Fq>> {
    _engine: PhantomData<(E, S)>,
}

impl<E: PairingEngine, S: FiatShamirRng<E::Fr, E::Fq>> SonicKZG10<E, S> {
    pub fn setup<R: RngCore>(max_degree: usize, rng: &mut R) -> Result<UniversalParams<E>, PCError> {
        kzg10::KZG10::setup(max_degree, &kzg10::KZG10DegreeBoundsConfig::MARLIN, true, rng).map_err(Into::into)
    }

    pub fn trim(
        pp: &UniversalParams<E>,
        supported_degree: usize,
        supported_lagrange_sizes: impl IntoIterator<Item = usize>,
        supported_hiding_bound: usize,
        enforced_degree_bounds: Option<&[usize]>,
    ) -> Result<(CommitterKey<E>, VerifierKey<E>), PCError> {
        let trim_time = start_timer!(|| "Trimming public parameters");
        let mut max_degree = pp.max_degree();
        if supported_degree > max_degree {
            pp.download_up_to(supported_degree).map_err(|_| PCError::TrimmingDegreeTooLarge)?;
            max_degree = pp.max_degree();
        }

        let enforced_degree_bounds = enforced_degree_bounds.map(|bounds| {
            let mut v = bounds.to_vec();
            v.sort_unstable();
            v.dedup();
            v
        });

        let (shifted_powers_of_beta_g, shifted_powers_of_beta_times_gamma_g) = if let Some(enforced_degree_bounds) =
            enforced_degree_bounds.as_ref()
        {
            if enforced_degree_bounds.is_empty() {
                (None, None)
            } else {
                let highest_enforced_degree_bound = *enforced_degree_bounds.last().unwrap();
                if highest_enforced_degree_bound > supported_degree {
                    return Err(PCError::UnsupportedDegreeBound(highest_enforced_degree_bound));
                }

                let lowest_shift_degree = max_degree - highest_enforced_degree_bound;

                let shifted_ck_time = start_timer!(|| format!(
                    "Constructing `shifted_powers_of_beta_g` of size {}",
                    max_degree - lowest_shift_degree + 1
                ));

                let shifted_powers_of_beta_g = pp.powers_of_beta_g(lowest_shift_degree, pp.max_degree() + 1).to_vec();
                let mut shifted_powers_of_beta_times_gamma_g = BTreeMap::new();
                // Also add degree 0.
                let _max_gamma_g = pp.get_powers_times_gamma_g().keys().last().unwrap();
                for degree_bound in enforced_degree_bounds {
                    let shift_degree = max_degree - degree_bound;
                    let mut powers_for_degree_bound = Vec::with_capacity((max_degree + 2).saturating_sub(shift_degree));
                    for i in 0..=supported_hiding_bound + 1 {
                        // We have an additional degree in `powers_of_beta_times_gamma_g` beyond `powers_of_beta_g`.
                        if shift_degree + i < max_degree + 2 {
                            powers_for_degree_bound.push(pp.get_powers_times_gamma_g()[&(shift_degree + i)]);
                        }
                    }
                    shifted_powers_of_beta_times_gamma_g.insert(*degree_bound, powers_for_degree_bound);
                }

                end_timer!(shifted_ck_time);

                (Some(shifted_powers_of_beta_g), Some(shifted_powers_of_beta_times_gamma_g))
            }
        } else {
            (None, None)
        };

        let powers_of_beta_g = pp.powers_of_beta_g(0, supported_degree + 1).to_vec();
        let powers_of_beta_times_gamma_g =
            (0..=supported_hiding_bound + 1).map(|i| pp.get_powers_times_gamma_g()[&i]).collect();

        let mut lagrange_bases_at_beta_g = BTreeMap::new();
        for size in supported_lagrange_sizes {
            if !size.is_power_of_two() {
                return Err(PCError::LagrangeBasisSizeIsNotPowerOfTwo);
            }
            if size > pp.max_degree() + 1 {
                return Err(PCError::LagrangeBasisSizeIsTooLarge);
            }
            let domain = crate::fft::EvaluationDomain::new(size).unwrap();
            let lagrange_basis_at_beta_g = pp.lagrange_basis(domain);
            assert!(lagrange_basis_at_beta_g.len().is_power_of_two());
            lagrange_bases_at_beta_g.insert(domain.size(), lagrange_basis_at_beta_g);
        }

        let ck = CommitterKey {
            powers_of_beta_g,
            lagrange_bases_at_beta_g,
            powers_of_beta_times_gamma_g,
            shifted_powers_of_beta_g,
            shifted_powers_of_beta_times_gamma_g,
            enforced_degree_bounds,
            max_degree,
        };

        let g = pp.power_of_beta_g(0);
        let h = pp.h;
        let beta_h = pp.beta_h;
        let gamma_g = pp.get_powers_times_gamma_g()[&0];
        let prepared_h = pp.prepared_h.clone();
        let prepared_beta_h = pp.prepared_beta_h.clone();

        let degree_bounds_and_neg_powers_of_h = if pp.inverse_neg_powers_of_beta_h.is_empty() {
            None
        } else {
            Some(
                pp.inverse_neg_powers_of_beta_h
                    .iter()
                    .map(|(d, affine)| (*d, *affine))
                    .collect::<Vec<(usize, E::G2Affine)>>(),
            )
        };

        let degree_bounds_and_prepared_neg_powers_of_h =
            degree_bounds_and_neg_powers_of_h.as_ref().map(|degree_bounds_and_neg_powers_of_h| {
                degree_bounds_and_neg_powers_of_h
                    .iter()
                    .map(|(d, affine)| (*d, affine.prepare()))
                    .collect::<Vec<(usize, <E::G2Affine as PairingCurve>::Prepared)>>()
            });

        let kzg10_vk = kzg10::VerifierKey::<E> { g, gamma_g, h, beta_h, prepared_h, prepared_beta_h };

        let vk = VerifierKey {
            vk: kzg10_vk,
            degree_bounds_and_neg_powers_of_h,
            degree_bounds_and_prepared_neg_powers_of_h,
            supported_degree,
            max_degree,
        };

        end_timer!(trim_time);
        Ok((ck, vk))
    }

    /// Outputs a commitments to `polynomials`. If `polynomials[i].is_hiding()`,
    /// then the `i`-th commitment is hiding up to `polynomials.hiding_bound()` queries.
    /// `rng` should not be `None` if `polynomials[i].is_hiding() == true` for any `i`.
    ///
    /// If for some `i`, `polynomials[i].is_hiding() == false`, then the
    /// corresponding randomness is `Randomness<E>::empty()`.
    ///
    /// If for some `i`, `polynomials[i].degree_bound().is_some()`, then that
    /// polynomial will have the corresponding degree bound enforced.
    #[allow(clippy::type_complexity)]
    pub fn commit<'a>(
        ck: &CommitterKey<E>,
        polynomials: impl IntoIterator<Item = LabeledPolynomialWithBasis<'a, E::Fr>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Vec<LabeledCommitment<Commitment<E>>>, Vec<Randomness<E>>), PCError> {
        Self::commit_with_terminator(ck, polynomials, &AtomicBool::new(false), rng)
    }

    /// Outputs a commitment to `polynomial`.
    #[allow(clippy::type_complexity)]
    pub fn commit_with_terminator<'a>(
        ck: &CommitterKey<E>,
        polynomials: impl IntoIterator<Item = LabeledPolynomialWithBasis<'a, E::Fr>>,
        terminator: &AtomicBool,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Vec<LabeledCommitment<Commitment<E>>>, Vec<Randomness<E>>), PCError> {
        let rng = &mut OptionalRng(rng);
        let commit_time = start_timer!(|| "Committing to polynomials");
        let mut labeled_comms: Vec<LabeledCommitment<Commitment<E>>> = Vec::new();
        let mut randomness: Vec<Randomness<E>> = Vec::new();

        let mut pool = snarkvm_utilities::ExecutionPool::<Result<_, _>>::new();
        for p in polynomials {
            if terminator.load(Ordering::Relaxed) {
                return Err(PCError::Terminated);
            }
            let seed = rng.0.as_mut().map(|r| {
                let mut seed = [0u8; 32];
                r.fill_bytes(&mut seed);
                seed
            });

            kzg10::KZG10::<E>::check_degrees_and_bounds(
                ck.supported_degree(),
                ck.max_degree,
                ck.enforced_degree_bounds.as_deref(),
                p.clone(),
            )?;
            let degree_bound = p.degree_bound();
            let hiding_bound = p.hiding_bound();
            let label = p.label().clone();

            pool.add_job(move || {
                let mut rng = seed.map(rand::rngs::StdRng::from_seed);
                let commit_time = start_timer!(|| format!(
                    "Polynomial {} of degree {}, degree bound {:?}, and hiding bound {:?}",
                    label,
                    p.degree(),
                    degree_bound,
                    hiding_bound,
                ));

                #[allow(clippy::or_fun_call)]
                let (comm, rand) = p
                    .sum()
                    .map(move |p| {
                        let rng_ref = rng.as_mut().map(|s| s as _);
                        match p {
                            PolynomialWithBasis::Lagrange { evaluations } => {
                                let domain = crate::fft::EvaluationDomain::new(evaluations.evaluations.len()).unwrap();
                                let lagrange_basis = ck
                                    .lagrange_basis(domain)
                                    .ok_or(PCError::UnsupportedLagrangeBasisSize(domain.size()))?;
                                assert!(domain.size().is_power_of_two());
                                assert!(lagrange_basis.size().is_power_of_two());
                                kzg10::KZG10::commit_lagrange(
                                    &lagrange_basis,
                                    &evaluations.evaluations,
                                    hiding_bound,
                                    terminator,
                                    rng_ref,
                                )
                            }
                            PolynomialWithBasis::Monomial { polynomial, degree_bound } => {
                                let powers = if let Some(degree_bound) = degree_bound {
                                    ck.shifted_powers_of_beta_g(degree_bound).unwrap()
                                } else {
                                    ck.powers()
                                };

                                kzg10::KZG10::commit(&powers, &polynomial, hiding_bound, terminator, rng_ref)
                            }
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .fold((E::G1Projective::zero(), Randomness::empty()), |mut a, b| {
                        a.0.add_assign_mixed(&b.0.0);
                        a.1 += (E::Fr::one(), &b.1);
                        a
                    });
                let comm = kzg10::Commitment(comm.to_affine());

                end_timer!(commit_time);
                Ok((LabeledCommitment::new(label.to_string(), comm, degree_bound), rand))
            });
        }
        let results: Vec<Result<_, PCError>> = pool.execute_all();
        for result in results {
            let (comm, rand) = result?;
            labeled_comms.push(comm);
            randomness.push(rand);
        }

        end_timer!(commit_time);
        Ok((labeled_comms, randomness))
    }

    pub fn combine_for_open<'a>(
        ck: &CommitterKey<E>,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<E::Fr>>,
        rands: impl IntoIterator<Item = &'a Randomness<E>>,
        fs_rng: &mut S,
    ) -> Result<(DensePolynomial<E::Fr>, Randomness<E>), PCError>
    where
        Randomness<E>: 'a,
        Commitment<E>: 'a,
    {
        Ok(Self::combine_polynomials(labeled_polynomials.into_iter().zip_eq(rands).map(|(p, r)| {
            let enforced_degree_bounds: Option<&[usize]> = ck.enforced_degree_bounds.as_deref();

            kzg10::KZG10::<E>::check_degrees_and_bounds(
                ck.supported_degree(),
                ck.max_degree,
                enforced_degree_bounds,
                p,
            )
            .unwrap();
            let challenge = fs_rng.squeeze_short_nonnative_field_element().unwrap();
            (challenge, p.polynomial().as_dense().unwrap(), r)
        })))
    }

    /// On input a list of labeled polynomials and a query set, `open` outputs a proof of evaluation
    /// of the polynomials at the points in the query set.
    pub fn batch_open<'a>(
        ck: &CommitterKey<E>,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<E::Fr>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Commitment<E>>>,
        query_set: &QuerySet<E::Fr>,
        rands: impl IntoIterator<Item = &'a Randomness<E>>,
        fs_rng: &mut S,
    ) -> Result<BatchProof<E>, PCError>
    where
        Randomness<E>: 'a,
        Commitment<E>: 'a,
    {
        let poly_rand_comm: HashMap<_, _> = labeled_polynomials
            .into_iter()
            .zip_eq(rands)
            .zip_eq(commitments.into_iter())
            .map(|((poly, r), comm)| (poly.label(), (poly, r, comm)))
            .collect();

        let open_time = start_timer!(|| format!(
            "Opening {} polynomials at query set of size {}",
            poly_rand_comm.len(),
            query_set.len(),
        ));

        let mut query_to_labels_map = BTreeMap::new();

        for (label, (point_name, point)) in query_set.iter() {
            let labels = query_to_labels_map.entry(point_name).or_insert((point, BTreeSet::new()));
            labels.1.insert(label);
        }

        let mut pool = snarkvm_utilities::ExecutionPool::<_>::with_capacity(query_to_labels_map.len());
        for (_point_name, (&query, labels)) in query_to_labels_map.into_iter() {
            let mut query_polys = Vec::with_capacity(labels.len());
            let mut query_rands = Vec::with_capacity(labels.len());
            let mut query_comms = Vec::with_capacity(labels.len());

            for label in labels {
                let (polynomial, rand, comm) =
                    poly_rand_comm.get(label).ok_or(PCError::MissingPolynomial { label: label.to_string() })?;

                query_polys.push(*polynomial);
                query_rands.push(*rand);
                query_comms.push(*comm);
            }
            let (polynomial, rand) = Self::combine_for_open(ck, query_polys, query_rands, fs_rng)?;

            pool.add_job(move || {
                let proof_time = start_timer!(|| "Creating proof");
                let proof = kzg10::KZG10::open(&ck.powers(), &polynomial, query, &rand);
                end_timer!(proof_time);
                proof
            });
        }
        let batch_proof = pool.execute_all().into_iter().collect::<Result<_, _>>().map(BatchProof);
        end_timer!(open_time);

        batch_proof
    }

    pub fn batch_check<'a>(
        vk: &VerifierKey<E>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Commitment<E>>>,
        query_set: &QuerySet<E::Fr>,
        values: &Evaluations<E::Fr>,
        proof: &BatchProof<E>,
        fs_rng: &mut S,
    ) -> Result<bool, PCError>
    where
        Commitment<E>: 'a,
    {
        let commitments: BTreeMap<_, _> = commitments.into_iter().map(|c| (c.label().to_owned(), c)).collect();
        let mut query_to_labels_map = BTreeMap::new();

        for (label, (point_name, point)) in query_set.iter() {
            let labels = query_to_labels_map.entry(point_name).or_insert((point, BTreeSet::new()));
            labels.1.insert(label);
        }

        assert_eq!(proof.0.len(), query_to_labels_map.len());

        let mut randomizer = E::Fr::one();

        let mut combined_comms = BTreeMap::new();
        let mut combined_witness = E::G1Projective::zero();
        let mut combined_adjusted_witness = E::G1Projective::zero();

        let mut batch_kzg_check_fs_rng = S::new();
        batch_kzg_check_fs_rng
            .absorb_nonnative_field_elements(query_set.iter().map(|(_, (_, q))| *q), OptimizationType::Weight);
        batch_kzg_check_fs_rng.absorb_nonnative_field_elements(values.values().copied(), OptimizationType::Weight);
        proof.absorb_into_sponge(&mut batch_kzg_check_fs_rng)?;

        for ((_query_name, (query, labels)), p) in query_to_labels_map.into_iter().zip_eq(&proof.0) {
            let mut comms_to_combine: Vec<&'_ LabeledCommitment<_>> = Vec::new();
            let mut values_to_combine = Vec::new();
            for label in labels.into_iter() {
                let commitment =
                    commitments.get(label).ok_or(PCError::MissingPolynomial { label: label.to_string() })?;

                let v_i = values
                    .get(&(label.clone(), *query))
                    .ok_or(PCError::MissingEvaluation { label: label.to_string() })?;

                comms_to_combine.push(commitment);
                values_to_combine.push(*v_i);
            }

            Self::accumulate_elems(
                &mut combined_comms,
                &mut combined_witness,
                &mut combined_adjusted_witness,
                vk,
                comms_to_combine.into_iter(),
                *query,
                values_to_combine.into_iter(),
                p,
                Some(randomizer),
                fs_rng,
            );

            randomizer = batch_kzg_check_fs_rng.squeeze_short_nonnative_field_element()?;
        }

        Self::check_elems(combined_comms, combined_witness, combined_adjusted_witness, vk)
    }

    pub fn open_combinations<'a>(
        ck: &CommitterKey<E>,
        linear_combinations: impl IntoIterator<Item = &'a LinearCombination<E::Fr>>,
        polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<E::Fr>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Commitment<E>>>,
        query_set: &QuerySet<E::Fr>,
        rands: impl IntoIterator<Item = &'a Randomness<E>>,
        fs_rng: &mut S,
    ) -> Result<BatchLCProof<E>, PCError>
    where
        Randomness<E>: 'a,
        Commitment<E>: 'a,
    {
        let label_map = polynomials
            .into_iter()
            .zip_eq(rands)
            .zip_eq(commitments)
            .map(|((p, r), c)| (p.label(), (p, r, c)))
            .collect::<BTreeMap<_, _>>();

        let mut lc_polynomials = Vec::new();
        let mut lc_randomness = Vec::new();
        let mut lc_commitments = Vec::new();
        let mut lc_info = Vec::new();

        for lc in linear_combinations {
            let lc_label = lc.label().clone();
            let mut poly = DensePolynomial::zero();
            let mut degree_bound = None;
            let mut hiding_bound = None;

            let mut randomness = Randomness::empty();
            let mut coeffs_and_comms = Vec::new();

            let num_polys = lc.len();
            for (coeff, label) in lc.iter().filter(|(_, l)| !l.is_one()) {
                let label: &String = label.try_into().expect("cannot be one!");
                let &(cur_poly, cur_rand, cur_comm) =
                    label_map.get(label).ok_or(PCError::MissingPolynomial { label: label.to_string() })?;
                if num_polys == 1 && cur_poly.degree_bound().is_some() {
                    assert!(coeff.is_one(), "Coefficient must be one for degree-bounded equations");
                    degree_bound = cur_poly.degree_bound();
                } else if cur_poly.degree_bound().is_some() {
                    return Err(PCError::EquationHasDegreeBounds(lc_label));
                }
                // Some(_) > None, always.
                hiding_bound = core::cmp::max(hiding_bound, cur_poly.hiding_bound());
                poly += (*coeff, cur_poly.polynomial());
                randomness += (*coeff, cur_rand);
                coeffs_and_comms.push((*coeff, cur_comm.commitment()));
            }

            let lc_poly = LabeledPolynomial::new(lc_label.clone(), poly, degree_bound, hiding_bound);
            lc_polynomials.push(lc_poly);
            lc_randomness.push(randomness);
            lc_commitments.push(Self::combine_commitments(coeffs_and_comms));
            lc_info.push((lc_label, degree_bound));
        }

        let comms = Self::normalize_commitments(lc_commitments);
        let lc_commitments = lc_info
            .into_iter()
            .zip_eq(comms)
            .map(|((label, d), c)| LabeledCommitment::new(label, c, d))
            .collect::<Vec<_>>();

        let proof = Self::batch_open(
            ck,
            lc_polynomials.iter(),
            lc_commitments.iter(),
            query_set,
            lc_randomness.iter(),
            fs_rng,
        )?;

        Ok(BatchLCProof { proof, evaluations: None })
    }

    /// Checks that `values` are the true evaluations at `query_set` of the polynomials
    /// committed in `labeled_commitments`.
    pub fn check_combinations<'a>(
        vk: &VerifierKey<E>,
        linear_combinations: impl IntoIterator<Item = &'a LinearCombination<E::Fr>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Commitment<E>>>,
        query_set: &QuerySet<E::Fr>,
        evaluations: &Evaluations<E::Fr>,
        proof: &BatchLCProof<E>,
        fs_rng: &mut S,
    ) -> Result<bool, PCError>
    where
        Commitment<E>: 'a,
    {
        let BatchLCProof { proof, .. } = proof;
        let label_comm_map = commitments.into_iter().map(|c| (c.label(), c)).collect::<BTreeMap<_, _>>();

        let mut lc_commitments = Vec::new();
        let mut lc_info = Vec::new();
        let mut evaluations = evaluations.clone();

        let lc_processing_time = start_timer!(|| "Combining commitments");
        for lc in linear_combinations {
            let lc_label = lc.label().clone();
            let num_polys = lc.len();

            let mut degree_bound = None;
            let mut coeffs_and_comms = Vec::new();

            for (coeff, label) in lc.iter() {
                if label.is_one() {
                    for (&(ref label, _), ref mut eval) in evaluations.iter_mut() {
                        if label == &lc_label {
                            **eval -= coeff;
                        }
                    }
                } else {
                    let label: &String = label.try_into().unwrap();
                    let &cur_comm =
                        label_comm_map.get(label).ok_or(PCError::MissingPolynomial { label: label.to_string() })?;

                    if num_polys == 1 && cur_comm.degree_bound().is_some() {
                        assert!(coeff.is_one(), "Coefficient must be one for degree-bounded equations");
                        degree_bound = cur_comm.degree_bound();
                    } else if cur_comm.degree_bound().is_some() {
                        return Err(PCError::EquationHasDegreeBounds(lc_label));
                    }
                    coeffs_and_comms.push((*coeff, cur_comm.commitment()));
                }
            }
            let lc_time = start_timer!(|| format!("Combining {} commitments for {}", num_polys, lc_label));
            lc_commitments.push(Self::combine_commitments(coeffs_and_comms));
            end_timer!(lc_time);
            lc_info.push((lc_label, degree_bound));
        }
        end_timer!(lc_processing_time);
        let combined_comms_norm_time = start_timer!(|| "Normalizing commitments");
        let comms = Self::normalize_commitments(lc_commitments);
        let lc_commitments = lc_info
            .into_iter()
            .zip_eq(comms)
            .map(|((label, d), c)| LabeledCommitment::new(label, c, d))
            .collect::<Vec<_>>();
        end_timer!(combined_comms_norm_time);

        Self::batch_check(vk, &lc_commitments, query_set, &evaluations, proof, fs_rng)
    }
}

impl<E: PairingEngine, S: FiatShamirRng<E::Fr, E::Fq>> SonicKZG10<E, S> {
    fn combine_polynomials<'a>(
        coeffs_polys_rands: impl IntoIterator<Item = (E::Fr, &'a DensePolynomial<E::Fr>, &'a Randomness<E>)>,
    ) -> (DensePolynomial<E::Fr>, Randomness<E>) {
        let mut combined_poly = DensePolynomial::zero();
        let mut combined_rand = Randomness::empty();
        for (coeff, poly, rand) in coeffs_polys_rands {
            if coeff.is_one() {
                combined_poly += poly;
                combined_rand += rand;
            } else {
                combined_poly += (coeff, poly);
                combined_rand += (coeff, rand);
            }
        }
        (combined_poly, combined_rand)
    }

    /// MSM for `commitments` and `coeffs`
    fn combine_commitments<'a>(
        coeffs_and_comms: impl IntoIterator<Item = (E::Fr, &'a Commitment<E>)>,
    ) -> E::G1Projective {
        let mut combined_comm = E::G1Projective::zero();
        for (coeff, comm) in coeffs_and_comms {
            if coeff.is_one() {
                combined_comm.add_assign_mixed(&comm.0);
            } else {
                combined_comm += &comm.0.mul(coeff);
            }
        }
        combined_comm
    }

    fn normalize_commitments(commitments: Vec<E::G1Projective>) -> impl Iterator<Item = Commitment<E>> {
        let comms = E::G1Projective::batch_normalization_into_affine(commitments);
        comms.into_iter().map(|c| kzg10::Commitment(c))
    }
}

impl<E: PairingEngine, S: FiatShamirRng<E::Fr, E::Fq>> SonicKZG10<E, S> {
    #[allow(clippy::too_many_arguments)]
    fn accumulate_elems<'a>(
        combined_comms: &mut BTreeMap<Option<usize>, E::G1Projective>,
        combined_witness: &mut E::G1Projective,
        combined_adjusted_witness: &mut E::G1Projective,
        vk: &VerifierKey<E>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Commitment<E>>>,
        point: E::Fr,
        values: impl IntoIterator<Item = E::Fr>,
        proof: &kzg10::Proof<E>,
        randomizer: Option<E::Fr>,
        fs_rng: &mut S,
    ) {
        let acc_time = start_timer!(|| "Accumulating elements");
        // Keeps track of running combination of values
        let mut combined_values = E::Fr::zero();

        // Iterates through all of the commitments and accumulates common degree_bound elements in a BTreeMap
        for (labeled_comm, value) in commitments.into_iter().zip_eq(values) {
            let curr_challenge = fs_rng.squeeze_short_nonnative_field_element().unwrap();

            combined_values += &(value * curr_challenge);

            let comm = labeled_comm.commitment();
            let degree_bound = labeled_comm.degree_bound();

            // Applying opening challenge and randomness (used in batch_checking)
            let mut comm_with_challenge: E::G1Projective = comm.0.mul(curr_challenge);

            if let Some(randomizer) = randomizer {
                comm_with_challenge = comm_with_challenge.mul(randomizer);
            }

            // Accumulate values in the BTreeMap
            *combined_comms.entry(degree_bound).or_insert_with(E::G1Projective::zero) += &comm_with_challenge;
        }

        // Push expected results into list of elems. Power will be the negative of the expected power
        let mut adjusted_witness = vk.vk.g.mul(combined_values) - proof.w.mul(point);
        if let Some(random_v) = proof.random_v {
            adjusted_witness += &vk.vk.gamma_g.mul(random_v);
        }

        let (witness, adjusted_witness) = if let Some(randomizer) = randomizer {
            (proof.w.mul(randomizer), adjusted_witness.mul(randomizer))
        } else {
            (proof.w.to_projective(), adjusted_witness)
        };

        *combined_witness += witness;
        *combined_adjusted_witness += adjusted_witness;
        end_timer!(acc_time);
    }

    #[allow(clippy::type_complexity)]
    fn check_elems(
        combined_comms: BTreeMap<Option<usize>, E::G1Projective>,
        combined_witness: E::G1Projective,
        combined_adjusted_witness: E::G1Projective,
        vk: &VerifierKey<E>,
    ) -> Result<bool, PCError> {
        let check_time = start_timer!(|| "Checking elems");
        let mut g1_projective_elems = Vec::with_capacity(combined_comms.len() + 2);
        let mut g2_prepared_elems = Vec::with_capacity(combined_comms.len() + 2);

        for (degree_bound, comm) in combined_comms.into_iter() {
            let shift_power = if let Some(degree_bound) = degree_bound {
                vk.get_prepared_shift_power(degree_bound).ok_or(PCError::UnsupportedDegreeBound(degree_bound))?
            } else {
                vk.vk.prepared_h.clone()
            };

            g1_projective_elems.push(comm);
            g2_prepared_elems.push(shift_power);
        }

        g1_projective_elems.push(-combined_adjusted_witness);
        g2_prepared_elems.push(vk.vk.prepared_h.clone());

        g1_projective_elems.push(-combined_witness);
        g2_prepared_elems.push(vk.vk.prepared_beta_h.clone());

        let g1_prepared_elems_iter = E::G1Projective::batch_normalization_into_affine(g1_projective_elems)
            .into_iter()
            .map(|a| a.prepare())
            .collect::<Vec<_>>();

        let g1_g2_prepared = g1_prepared_elems_iter.iter().zip_eq(g2_prepared_elems.iter());
        let is_one: bool = E::product_of_pairings(g1_g2_prepared).is_one();
        end_timer!(check_time);
        Ok(is_one)
    }
}

#[cfg(test)]
mod tests {
    #![allow(non_camel_case_types)]

    use super::{CommitterKey, SonicKZG10};
    use crate::{
        crypto_hash::PoseidonSponge,
        polycommit::test_templates::*,
        snark::marlin::FiatShamirAlgebraicSpongeRng,
    };
    use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
    use snarkvm_utilities::{rand::test_rng, FromBytes, ToBytes};

    use rand::distributions::Distribution;

    type Sponge = FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq, 6, 1>>;
    type PC_Bls12_377 = SonicKZG10<Bls12_377, Sponge>;

    #[test]
    fn test_committer_key_serialization() {
        let rng = &mut test_rng();
        let max_degree = rand::distributions::Uniform::from(8..=64).sample(rng);
        let supported_degree = rand::distributions::Uniform::from(1..=max_degree).sample(rng);

        let lagrange_size = |d: usize| if d.is_power_of_two() { d } else { d.next_power_of_two() >> 1 };

        let pp = PC_Bls12_377::setup(max_degree, rng).unwrap();

        let (ck, _vk) = PC_Bls12_377::trim(&pp, supported_degree, [lagrange_size(supported_degree)], 0, None).unwrap();

        let ck_bytes = ck.to_bytes_le().unwrap();
        let ck_recovered: CommitterKey<Bls12_377> = FromBytes::read_le(&ck_bytes[..]).unwrap();
        let ck_recovered_bytes = ck_recovered.to_bytes_le().unwrap();

        assert_eq!(&ck_bytes, &ck_recovered_bytes);
    }

    #[test]
    fn test_single_poly() {
        single_poly_test::<Bls12_377, Sponge>().expect("test failed for bls12-377");
    }

    #[test]
    fn test_quadratic_poly_degree_bound_multiple_queries() {
        quadratic_poly_degree_bound_multiple_queries_test::<Bls12_377, Sponge>().expect("test failed for bls12-377");
    }

    #[test]
    fn test_linear_poly_degree_bound() {
        linear_poly_degree_bound_test::<Bls12_377, Sponge>().expect("test failed for bls12-377");
    }

    #[test]
    fn test_single_poly_degree_bound() {
        single_poly_degree_bound_test::<Bls12_377, Sponge>().expect("test failed for bls12-377");
    }

    #[test]
    fn test_single_poly_degree_bound_multiple_queries() {
        single_poly_degree_bound_multiple_queries_test::<Bls12_377, Sponge>().expect("test failed for bls12-377");
    }

    #[test]
    fn test_two_polys_degree_bound_single_query() {
        two_polys_degree_bound_single_query_test::<Bls12_377, Sponge>().expect("test failed for bls12-377");
    }

    #[test]
    fn test_full_end_to_end() {
        full_end_to_end_test::<Bls12_377, Sponge>().expect("test failed for bls12-377");
        println!("Finished bls12-377");
    }

    #[test]
    fn test_single_equation() {
        single_equation_test::<Bls12_377, Sponge>().expect("test failed for bls12-377");
        println!("Finished bls12-377");
    }

    #[test]
    fn test_two_equation() {
        two_equation_test::<Bls12_377, Sponge>().expect("test failed for bls12-377");
        println!("Finished bls12-377");
    }

    #[test]
    fn test_two_equation_degree_bound() {
        two_equation_degree_bound_test::<Bls12_377, Sponge>().expect("test failed for bls12-377");
        println!("Finished bls12-377");
    }

    #[test]
    fn test_full_end_to_end_equation() {
        full_end_to_end_equation_test::<Bls12_377, Sponge>().expect("test failed for bls12-377");
        println!("Finished bls12-377");
    }

    #[test]
    #[should_panic]
    fn test_bad_degree_bound() {
        bad_degree_bound_test::<Bls12_377, Sponge>().expect("test failed for bls12-377");
        println!("Finished bls12-377");
    }

    #[test]
    fn test_lagrange_commitment() {
        crate::polycommit::test_templates::lagrange_test_template::<Bls12_377, Sponge>()
            .expect("test failed for bls12-377");
        println!("Finished bls12-377");
    }
}
