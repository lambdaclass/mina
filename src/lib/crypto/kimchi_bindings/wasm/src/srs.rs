use crate::wasm_flat_vector::WasmFlatVector;
use crate::wasm_vector::WasmVector;
use ark_poly::UVPolynomial;
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, Evaluations};
use paste::paste;
use poly_commitment::SRS as ISRS;
use poly_commitment::{commitment::b_poly_coefficients, srs::SRS};
use serde::{Deserialize, Serialize};
use std::ops::Deref;
use std::{
    fs::{File, OpenOptions},
    io::{BufReader, BufWriter, Seek, SeekFrom::Start},
    sync::Arc,
};
use wasm_bindgen::prelude::*;

macro_rules! impl_srs {
    ($name: ident,
     $WasmF: ty,
     $WasmG: ty,
     $F: ty,
     $G: ty,
     $WasmPolyComm: ty,
     $field_name: ident) => {
        paste! {
            #[wasm_bindgen]
            #[derive(Clone)]
            pub struct [<Wasm $field_name:camel Srs>](
                #[wasm_bindgen(skip)]
                pub Arc<SRS<$G>>);

            impl Deref for [<Wasm $field_name:camel Srs>] {
                type Target = Arc<SRS<$G>>;

                fn deref(&self) -> &Self::Target { &self.0 }
            }

            impl From<Arc<SRS<$G>>> for [<Wasm $field_name:camel Srs>] {
                fn from(x: Arc<SRS<$G>>) -> Self {
                    [<Wasm $field_name:camel Srs>](x)
                }
            }

            impl From<&Arc<SRS<$G>>> for [<Wasm $field_name:camel Srs>] {
                fn from(x: &Arc<SRS<$G>>) -> Self {
                    [<Wasm $field_name:camel Srs>](x.clone())
                }
            }

            impl From<[<Wasm $field_name:camel Srs>]> for Arc<SRS<$G>> {
                fn from(x: [<Wasm $field_name:camel Srs>]) -> Self {
                    x.0
                }
            }

            impl From<&[<Wasm $field_name:camel Srs>]> for Arc<SRS<$G>> {
                fn from(x: &[<Wasm $field_name:camel Srs>]) -> Self {
                    x.0.clone()
                }
            }

            impl<'a> From<&'a [<Wasm $field_name:camel Srs>]> for &'a Arc<SRS<$G>> {
                fn from(x: &'a [<Wasm $field_name:camel Srs>]) -> Self {
                    &x.0
                }
            }

            #[wasm_bindgen]
            pub fn [<$name:snake _create>](depth: i32) -> [<Wasm $field_name:camel Srs>] {
                Arc::new(SRS::create(depth as usize)).into()
            }

            #[wasm_bindgen]
            pub fn [<$name:snake _add_lagrange_basis>](
                srs: &[<Wasm $field_name:camel Srs>],
                log2_size: i32,
            ) {
                crate::rayon::run_in_pool(|| {
                    let ptr: &mut poly_commitment::srs::SRS<$G> =
                        unsafe { &mut *(std::sync::Arc::as_ptr(&srs) as *mut _) };
                    let domain = EvaluationDomain::<$F>::new(1 << (log2_size as usize)).expect("invalid domain size");
                    ptr.add_lagrange_basis(domain);
                });
            }

            #[wasm_bindgen]
            pub fn [<$name:snake _write>](
                append: Option<bool>,
                srs: &[<Wasm $field_name:camel Srs>],
                path: String,
            ) -> Result<(), JsValue> {
                let file = OpenOptions::new()
                    .append(append.unwrap_or(true))
                    .open(path)
                    .map_err(|err| {
                        JsValue::from_str(format!("caml_pasta_fp_urs_write: {}", err).as_str())
                    })?;
                let file = BufWriter::new(file);

                srs.0.serialize(&mut rmp_serde::Serializer::new(file))
                .map_err(|e| JsValue::from_str(format!("caml_pasta_fp_urs_write: {}", e).as_str()))
            }

            #[wasm_bindgen]
            pub fn [<$name:snake _read>](
                offset: Option<i32>,
                path: String,
            ) -> Result<Option<[<Wasm $field_name:camel Srs>]>, JsValue> {
                let file = File::open(path).map_err(|err| {
                    JsValue::from_str(format!("caml_pasta_fp_urs_read: {}", err).as_str())
                })?;
                let mut reader = BufReader::new(file);

                if let Some(offset) = offset {
                    reader.seek(Start(offset as u64)).map_err(|err| {
                        JsValue::from_str(format!("caml_pasta_fp_urs_read: {}", err).as_str())
                    })?;
                }

                // TODO: shouldn't we just error instead of returning None?
                let srs = match SRS::<$G>::deserialize(&mut rmp_serde::Deserializer::new(reader)) {
                    Ok(srs) => srs,
                    Err(_) => return Ok(None),
                };

                Ok(Some(Arc::new(srs).into()))
            }

            #[wasm_bindgen]
            pub fn [<$name:snake _lagrange_commitment>](
                srs: &[<Wasm $field_name:camel Srs>],
                domain_size: i32,
                i: i32,
            ) -> Result<$WasmPolyComm, JsValue> {
                let x_domain = EvaluationDomain::<$F>::new(domain_size as usize).ok_or_else(|| {
                    JsValue::from_str("caml_pasta_fp_urs_lagrange_commitment")
                })?;
                crate::rayon::run_in_pool(|| {
                    // We're single-threaded, so it's safe to grab this pointer as mutable.
                    // Do not try this at home.
                    let ptr: &mut poly_commitment::srs::SRS<$G> =
                        unsafe { &mut *(std::sync::Arc::as_ptr(&srs) as *mut _) };
                    ptr.add_lagrange_basis(x_domain);
                });

                Ok(srs.lagrange_bases[&x_domain.size()][i as usize].clone().into())
            }

            #[wasm_bindgen]
            pub fn [<$name:snake _commit_evaluations>](
                srs: &[<Wasm $field_name:camel Srs>],
                domain_size: i32,
                evals: WasmFlatVector<$WasmF>,
            ) -> Result<$WasmPolyComm, JsValue> {
                let x_domain = EvaluationDomain::<$F>::new(domain_size as usize).ok_or_else(|| {
                    JsValue::from_str("caml_pasta_fp_urs_commit_evaluations")
                })?;

                let evals = evals.into_iter().map(Into::into).collect();
                let p = Evaluations::<$F>::from_vec_and_domain(evals, x_domain).interpolate();

                Ok(srs.commit_non_hiding(&p, 1, None).into())
            }

            #[wasm_bindgen]
            pub fn [<$name:snake _b_poly_commitment>](
                srs: &[<Wasm $field_name:camel Srs>],
                chals: WasmFlatVector<$WasmF>,
            ) -> Result<$WasmPolyComm, JsValue> {
                let result = crate::rayon::run_in_pool(|| {
                    let chals: Vec<$F> = chals.into_iter().map(Into::into).collect();
                    let coeffs = b_poly_coefficients(&chals);
                    let p = DensePolynomial::<$F>::from_coefficients_vec(coeffs);
                    srs.commit_non_hiding(&p, 1, None)
                });
                Ok(result.into())
            }

            #[wasm_bindgen]
            pub fn [<$name:snake _batch_accumulator_check>](
                srs: &[<Wasm $field_name:camel Srs>],
                comms: WasmVector<$WasmG>,
                chals: WasmFlatVector<$WasmF>,
            ) -> bool {
                crate::rayon::run_in_pool(|| {
                    let comms: Vec<_> = comms.into_iter().map(Into::into).collect();
                    let chals: Vec<_> = chals.into_iter().map(Into::into).collect();
                    crate::urs_utils::batch_dlog_accumulator_check(&srs, &comms, &chals)
                })
            }

            #[wasm_bindgen]
            pub fn [<$name:snake _batch_accumulator_generate>](
                srs: &[<Wasm $field_name:camel Srs>],
                comms: i32,
                chals: WasmFlatVector<$WasmF>,
            ) -> WasmVector<$WasmG> {
                crate::urs_utils::batch_dlog_accumulator_generate::<$G>(
                    &srs,
                    comms as usize,
                    &chals.into_iter().map(From::from).collect(),
                ).into_iter().map(Into::into).collect()
            }

            #[wasm_bindgen]
            pub fn [<$name:snake _h>](srs: &[<Wasm $field_name:camel Srs>]) -> $WasmG {
                srs.h.into()
            }
        }
    }
}

//
// Fp
//

pub mod fp {
    use std::collections::HashMap;

    use super::*;
    use crate::arkworks::{WasmGVesta as WasmG, WasmPastaFp};
    use crate::poly_comm::vesta::WasmFpPolyComm as WasmPolyComm;
    use mina_curves::pasta::{Fp, Vesta as G};
    use poly_commitment::PolyComm;

    impl_srs!(caml_fp_srs, WasmPastaFp, WasmG, Fp, G, WasmPolyComm, Fp);

    #[wasm_bindgen]
    pub fn caml_fp_srs_create_parallel(depth: i32) -> WasmFpSrs {
        crate::rayon::run_in_pool(|| Arc::new(SRS::<G>::create_parallel(depth as usize)).into())
    }

    // return the cloned srs in a form that we can store on the js side
    #[wasm_bindgen]
    pub fn caml_fp_srs_get(srs: &WasmFpSrs) -> WasmVector<WasmG> {
        // return a vector which consists of h, then all the gs
        let mut h_and_gs: Vec<WasmG> = vec![srs.0.h.clone().into()];
        h_and_gs.extend(srs.0.g.iter().map(|x: &G| WasmG::from(x.clone())));
        h_and_gs.into()
    }

    // set the srs from a vector of h and gs
    #[wasm_bindgen]
    pub fn caml_fp_srs_set(h_and_gs: WasmVector<WasmG>) -> WasmFpSrs {
        // return a vector which consists of h, then all the gs
        let mut h_and_gs: Vec<G> = h_and_gs.into_iter().map(|x| x.into()).collect();
        let h = h_and_gs.remove(0);
        let g = h_and_gs;
        let srs = SRS::<G> {
            h,
            g,
            lagrange_bases: HashMap::new(),
        };
        Arc::new(srs).into()
    }

    // maybe get lagrange commitment
    #[wasm_bindgen]
    pub fn caml_fp_srs_maybe_lagrange_commitment(
        srs: &WasmFpSrs,
        domain_size: i32,
        i: i32,
    ) -> Option<WasmPolyComm> {
        let bases = srs.0.lagrange_bases.get(&(domain_size as usize));
        bases.map(|bases| bases[i as usize].clone().into())
    }

    // set entire lagrange basis from input
    #[wasm_bindgen]
    pub fn caml_fp_srs_set_lagrange_basis(
        srs: &WasmFpSrs,
        domain_size: i32,
        input_bases: WasmVector<WasmPolyComm>,
    ) {
        let bases: Vec<PolyComm<G>> = input_bases.into_iter().map(Into::into).collect();

        // add to srs
        let ptr: &mut poly_commitment::srs::SRS<G> =
            unsafe { &mut *(std::sync::Arc::as_ptr(&srs) as *mut _) };
        ptr.lagrange_bases.insert(domain_size as usize, bases);
    }

    // compute & add lagrange basis internally, return the entire basis
    #[wasm_bindgen]
    pub fn caml_fp_srs_get_lagrange_basis(
        srs: &WasmFpSrs,
        domain_size: i32,
    ) -> WasmVector<WasmPolyComm> {
        // compute lagrange basis
        crate::rayon::run_in_pool(|| {
            let ptr: &mut poly_commitment::srs::SRS<G> =
                unsafe { &mut *(std::sync::Arc::as_ptr(&srs) as *mut _) };
            let domain =
                EvaluationDomain::<Fp>::new(domain_size as usize).expect("invalid domain size");
            ptr.add_lagrange_basis(domain);
        });
        let bases = &srs.0.lagrange_bases[&(domain_size as usize)];
        bases.into_iter().map(Into::into).collect()
    }
}

pub mod fq {
    use std::collections::HashMap;

    use super::*;
    use crate::arkworks::{WasmGPallas as WasmG, WasmPastaFq};
    use crate::poly_comm::pallas::WasmFqPolyComm as WasmPolyComm;
    use mina_curves::pasta::{Fq, Pallas as G};
    use poly_commitment::PolyComm;

    impl_srs!(caml_fq_srs, WasmPastaFq, WasmG, Fq, G, WasmPolyComm, Fq);

    #[wasm_bindgen]
    pub fn caml_fq_srs_create_parallel(depth: i32) -> WasmFqSrs {
        crate::rayon::run_in_pool(|| Arc::new(SRS::<G>::create_parallel(depth as usize)).into())
    }

    // return the cloned srs in a form that we can store on the js side
    #[wasm_bindgen]
    pub fn caml_fq_srs_get(srs: &WasmFqSrs) -> WasmVector<WasmG> {
        // return a vector which consists of h, then all the gs
        let mut h_and_gs: Vec<WasmG> = vec![srs.0.h.clone().into()];
        h_and_gs.extend(srs.0.g.iter().map(|x: &G| WasmG::from(x.clone())));
        h_and_gs.into()
    }

    // set the srs from a vector of h and gs
    #[wasm_bindgen]
    pub fn caml_fq_srs_set(h_and_gs: WasmVector<WasmG>) -> WasmFqSrs {
        // return a vector which consists of h, then all the gs
        let mut h_and_gs: Vec<G> = h_and_gs.into_iter().map(|x| x.into()).collect();
        let h = h_and_gs.remove(0);
        let g = h_and_gs;
        let srs = SRS::<G> {
            h,
            g,
            lagrange_bases: HashMap::new(),
        };
        Arc::new(srs).into()
    }

    // maybe get lagrange commitment
    #[wasm_bindgen]
    pub fn caml_fq_srs_maybe_lagrange_commitment(
        srs: &WasmFqSrs,
        domain_size: i32,
        i: i32,
    ) -> Option<WasmPolyComm> {
        let bases = srs.0.lagrange_bases.get(&(domain_size as usize));
        bases.map(|bases| bases[i as usize].clone().into())
    }

    // set entire lagrange basis from input
    #[wasm_bindgen]
    pub fn caml_fq_srs_set_lagrange_basis(
        srs: &WasmFqSrs,
        domain_size: i32,
        input_bases: WasmVector<WasmPolyComm>,
    ) {
        let bases: Vec<PolyComm<G>> = input_bases.into_iter().map(Into::into).collect();

        // add to srs
        let ptr: &mut poly_commitment::srs::SRS<G> =
            unsafe { &mut *(std::sync::Arc::as_ptr(&srs) as *mut _) };
        ptr.lagrange_bases.insert(domain_size as usize, bases);
    }

    // compute & add lagrange basis internally, return the entire basis
    #[wasm_bindgen]
    pub fn caml_fq_srs_get_lagrange_basis(
        srs: &WasmFqSrs,
        domain_size: i32,
    ) -> WasmVector<WasmPolyComm> {
        // compute lagrange basis
        crate::rayon::run_in_pool(|| {
            let ptr: &mut poly_commitment::srs::SRS<G> =
                unsafe { &mut *(std::sync::Arc::as_ptr(&srs) as *mut _) };
            let domain =
                EvaluationDomain::<Fq>::new(domain_size as usize).expect("invalid domain size");
            ptr.add_lagrange_basis(domain);
        });
        let bases = &srs.0.lagrange_bases[&(domain_size as usize)];
        bases.into_iter().map(Into::into).collect()
    }
}

//
// Bn254Fp
//

pub mod bn254_fp {
    use super::*;
    use crate::arkworks::{WasmBn254Fp, WasmGBn254};
    use crate::poly_comm::bn254::WasmBn254FpPolyComm as WasmPolyComm;
    use ark_ec::bn::Bn;
    use mina_curves::bn254::{Bn254, Fp};
    use poly_commitment::pairing_proof::PairingSRS;

    #[wasm_bindgen]
    #[derive(Clone)]
    pub struct WasmBn254FpSrs(#[wasm_bindgen(skip)] pub Arc<PairingSRS<Bn<ark_bn254::Parameters>>>);

    impl Deref for WasmBn254FpSrs {
        type Target = Arc<PairingSRS<Bn<ark_bn254::Parameters>>>;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl From<Arc<PairingSRS<Bn<ark_bn254::Parameters>>>> for WasmBn254FpSrs {
        fn from(x: Arc<PairingSRS<Bn<ark_bn254::Parameters>>>) -> Self {
            WasmBn254FpSrs(x)
        }
    }

    impl From<&Arc<PairingSRS<Bn<ark_bn254::Parameters>>>> for WasmBn254FpSrs {
        fn from(x: &Arc<PairingSRS<Bn<ark_bn254::Parameters>>>) -> Self {
            WasmBn254FpSrs(x.clone())
        }
    }

    impl From<WasmBn254FpSrs> for Arc<PairingSRS<Bn<ark_bn254::Parameters>>> {
        fn from(x: WasmBn254FpSrs) -> Self {
            x.0
        }
    }

    impl From<&WasmBn254FpSrs> for Arc<PairingSRS<Bn<ark_bn254::Parameters>>> {
        fn from(x: &WasmBn254FpSrs) -> Self {
            x.0.clone()
        }
    }

    impl<'a> From<&'a WasmBn254FpSrs> for &'a Arc<PairingSRS<Bn<ark_bn254::Parameters>>> {
        fn from(x: &'a WasmBn254FpSrs) -> Self {
            &x.0
        }
    }

    #[wasm_bindgen]
    pub fn caml_bn254_fp_srs_create(depth: i32) -> WasmBn254FpSrs {
        // This seed (42) is also used for generating a trusted setup in Solidity.
        let x = ark_bn254::Fr::from(42);
        Arc::new(PairingSRS::create(x, depth as usize)).into()
    }

    #[wasm_bindgen]
    pub fn caml_bn254_fp_srs_add_lagrange_basis(srs: &WasmBn254FpSrs, log2_size: i32) {
        crate::rayon::run_in_pool(|| {
            let ptr: &mut poly_commitment::srs::SRS<Bn254> =
                unsafe { &mut *(Arc::as_ptr(&Arc::new(&srs.full_srs)) as *mut _) };
            let domain = EvaluationDomain::<Fp>::new(1 << (log2_size as usize))
                .expect("invalid domain size");
            ptr.add_lagrange_basis(domain);
        });
    }

    #[wasm_bindgen]
    pub fn caml_bn254_fp_srs_write(
        append: Option<bool>,
        srs: &WasmBn254FpSrs,
        path: String,
    ) -> Result<(), JsValue> {
        let file = OpenOptions::new()
            .append(append.unwrap_or(true))
            .open(path)
            .map_err(|err| {
                JsValue::from_str(format!("caml_pasta_fp_urs_write: {}", err).as_str())
            })?;
        let file = BufWriter::new(file);

        srs.0
            .serialize(&mut rmp_serde::Serializer::new(file))
            .map_err(|e| JsValue::from_str(format!("caml_pasta_fp_urs_write: {}", e).as_str()))
    }

    #[wasm_bindgen]
    pub fn caml_bn254_fp_srs_read(
        offset: Option<i32>,
        path: String,
    ) -> Result<Option<WasmBn254FpSrs>, JsValue> {
        let file = File::open(path).map_err(|err| {
            JsValue::from_str(format!("caml_bn254_fp_urs_read: {}", err).as_str())
        })?;
        let mut reader = BufReader::new(file);

        if let Some(offset) = offset {
            reader.seek(Start(offset as u64)).map_err(|err| {
                JsValue::from_str(format!("caml_bn254_fp_urs_read: {}", err).as_str())
            })?;
        }

        // TODO: shouldn't we just error instead of returning None?
        let srs = match PairingSRS::<Bn<ark_bn254::Parameters>>::deserialize(
            &mut rmp_serde::Deserializer::new(reader),
        ) {
            Ok(srs) => srs,
            Err(_) => return Ok(None),
        };

        Ok(Some(Arc::new(srs).into()))
    }

    #[wasm_bindgen]
    pub fn caml_bn254_fp_srs_lagrange_commitment(
        srs: &WasmBn254FpSrs,
        domain_size: i32,
        i: i32,
    ) -> Result<WasmPolyComm, JsValue> {
        let x_domain = EvaluationDomain::<Fp>::new(domain_size as usize)
            .ok_or_else(|| JsValue::from_str("caml_pasta_fp_urs_lagrange_commitment"))?;
        {
            let ptr: &mut poly_commitment::srs::SRS<Bn254> =
                unsafe { &mut *(Arc::as_ptr(&Arc::new(&srs.full_srs)) as *mut _) };
            ptr.add_lagrange_basis(x_domain);
        }

        Ok(srs.full_srs.lagrange_bases[&x_domain.size()][i as usize]
            .clone()
            .into())
    }

    #[wasm_bindgen]
    pub fn caml_bn254_fp_srs_commit_evaluations(
        srs: &WasmBn254FpSrs,
        domain_size: i32,
        evals: WasmFlatVector<WasmBn254Fp>,
    ) -> Result<WasmPolyComm, JsValue> {
        let x_domain = EvaluationDomain::<Fp>::new(domain_size as usize)
            .ok_or_else(|| JsValue::from_str("caml_pasta_fp_urs_commit_evaluations"))?;

        let evals = evals.into_iter().map(Into::into).collect();
        let p = Evaluations::<Fp>::from_vec_and_domain(evals, x_domain).interpolate();

        Ok(srs.commit_non_hiding(&p, 1, None).into())
    }

    #[wasm_bindgen]
    pub fn caml_bn254_fp_srs_b_poly_commitment(
        srs: &WasmBn254FpSrs,
        chals: WasmFlatVector<WasmBn254Fp>,
    ) -> Result<WasmPolyComm, JsValue> {
        let result = crate::rayon::run_in_pool(|| {
            let chals: Vec<Fp> = chals.into_iter().map(Into::into).collect();
            let coeffs = b_poly_coefficients(&chals);
            let p = DensePolynomial::<Fp>::from_coefficients_vec(coeffs);
            srs.commit_non_hiding(&p, 1, None)
        });
        Ok(result.into())
    }

    #[wasm_bindgen]
    pub fn caml_bn254_fp_srs_batch_accumulator_check(
        srs: &WasmBn254FpSrs,
        comms: WasmVector<WasmGBn254>,
        chals: WasmFlatVector<WasmBn254Fp>,
    ) -> bool {
        let comms: Vec<_> = comms.into_iter().map(Into::into).collect();
        let chals: Vec<_> = chals.into_iter().map(Into::into).collect();
        crate::urs_utils::batch_dlog_accumulator_check(&srs.full_srs, &comms, &chals)
    }

    #[wasm_bindgen]
    pub fn caml_bn254_fp_srs_batch_accumulator_generate(
        srs: &WasmBn254FpSrs,
        comms: i32,
        chals: WasmFlatVector<WasmBn254Fp>,
    ) -> WasmVector<WasmGBn254> {
        crate::urs_utils::batch_dlog_accumulator_generate::<Bn254>(
            &srs.full_srs,
            comms as usize,
            &chals.into_iter().map(From::from).collect(),
        )
        .into_iter()
        .map(Into::into)
        .collect()
    }

    #[wasm_bindgen]
    pub fn caml_bn254_fp_srs_h(srs: &WasmBn254FpSrs) -> WasmGBn254 {
        srs.full_srs.h.into()
    }
}
