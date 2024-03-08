use crate::arkworks::bigint_256::{self, WasmBigInteger256};
use ark_ff::{
    fields::{Field, FpParameters, PrimeField, SquareRootField},
    FftField, One, UniformRand, Zero,
};
use ark_ff::{FromBytes, ToBytes};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain as Domain};
use mina_curves::bn254::{fields::fq::FqParameters as Fq_params, Fq};
use num_bigint::BigUint;
use rand::rngs::StdRng;
use std::cmp::Ordering::{Equal, Greater, Less};
use wasm_bindgen::convert::{FromWasmAbi, IntoWasmAbi, OptionFromWasmAbi, OptionIntoWasmAbi};
use wasm_bindgen::prelude::*;

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct WasmBn254Fq(pub Fq);

impl crate::wasm_flat_vector::FlatVectorElem for WasmBn254Fq {
    const FLATTENED_SIZE: usize = std::mem::size_of::<Fq>();
    fn flatten(self) -> Vec<u8> {
        let mut bytes: Vec<u8> = Vec::with_capacity(Self::FLATTENED_SIZE);
        self.0.write(&mut bytes).unwrap();
        bytes
    }
    fn unflatten(flat: Vec<u8>) -> Self {
        WasmBn254Fq(FromBytes::read(flat.as_slice()).unwrap())
    }
}

impl From<Fq> for WasmBn254Fq {
    fn from(x: Fq) -> Self {
        WasmBn254Fq(x)
    }
}

impl From<WasmBn254Fq> for Fq {
    fn from(x: WasmBn254Fq) -> Self {
        x.0
    }
}

impl<'a> From<&'a WasmBn254Fq> for &'a Fq {
    fn from(x: &'a WasmBn254Fq) -> Self {
        &x.0
    }
}

impl wasm_bindgen::describe::WasmDescribe for WasmBn254Fq {
    fn describe() {
        <Vec<u8> as wasm_bindgen::describe::WasmDescribe>::describe()
    }
}

impl FromWasmAbi for WasmBn254Fq {
    type Abi = <Vec<u8> as FromWasmAbi>::Abi;
    unsafe fn from_abi(js: Self::Abi) -> Self {
        let bytes: Vec<u8> = FromWasmAbi::from_abi(js);
        WasmBn254Fq(FromBytes::read(bytes.as_slice()).unwrap())
    }
}

impl IntoWasmAbi for WasmBn254Fq {
    type Abi = <Vec<u8> as FromWasmAbi>::Abi;
    fn into_abi(self) -> Self::Abi {
        let mut bytes: Vec<u8> = vec![];
        self.0.write(&mut bytes).unwrap();
        bytes.into_abi()
    }
}

impl OptionIntoWasmAbi for WasmBn254Fq {
    fn none() -> Self::Abi {
        <Vec<u8> as OptionIntoWasmAbi>::none()
    }
}

impl OptionFromWasmAbi for WasmBn254Fq {
    fn is_none(abi: &Self::Abi) -> bool {
        <Vec<u8> as OptionFromWasmAbi>::is_none(abi)
    }
}

#[wasm_bindgen]
pub fn caml_bn254_fq_size_in_bits() -> isize {
    Fq_params::MODULUS_BITS as isize
}

#[wasm_bindgen]
pub fn caml_bn254_fq_size() -> WasmBigInteger256 {
    WasmBigInteger256(Fq_params::MODULUS)
}

#[wasm_bindgen]
pub fn caml_bn254_fq_add(x: WasmBn254Fq, y: WasmBn254Fq) -> WasmBn254Fq {
    WasmBn254Fq(x.0 + y.0)
}

#[wasm_bindgen]
pub fn caml_bn254_fq_sub(x: WasmBn254Fq, y: WasmBn254Fq) -> WasmBn254Fq {
    WasmBn254Fq(x.0 - y.0)
}

#[wasm_bindgen]
pub fn caml_bn254_fq_negate(x: WasmBn254Fq) -> WasmBn254Fq {
    WasmBn254Fq(-x.0)
}

#[wasm_bindgen]
pub fn caml_bn254_fq_mul(x: WasmBn254Fq, y: WasmBn254Fq) -> WasmBn254Fq {
    WasmBn254Fq(x.0 * y.0)
}

#[wasm_bindgen]
pub fn caml_bn254_fq_div(x: WasmBn254Fq, y: WasmBn254Fq) -> WasmBn254Fq {
    WasmBn254Fq(x.0 / y.0)
}

#[wasm_bindgen]
pub fn caml_bn254_fq_inv(x: WasmBn254Fq) -> Option<WasmBn254Fq> {
    x.0.inverse().map(WasmBn254Fq)
}

#[wasm_bindgen]
pub fn caml_bn254_fq_square(x: WasmBn254Fq) -> WasmBn254Fq {
    WasmBn254Fq(x.0.square())
}

#[wasm_bindgen]
pub fn caml_bn254_fq_is_square(x: WasmBn254Fq) -> bool {
    let s = x.0.pow(Fq_params::MODULUS_MINUS_ONE_DIV_TWO);
    s.is_zero() || s.is_one()
}

#[wasm_bindgen]
pub fn caml_bn254_fq_sqrt(x: WasmBn254Fq) -> Option<WasmBn254Fq> {
    x.0.sqrt().map(WasmBn254Fq)
}

#[wasm_bindgen]
pub fn caml_bn254_fq_of_int(i: i32) -> WasmBn254Fq {
    WasmBn254Fq(Fq::from(i as u64))
}

#[wasm_bindgen]
pub fn caml_bn254_fq_to_string(x: WasmBn254Fq) -> String {
    bigint_256::to_biguint(&x.0.into_repr()).to_string()
}

#[wasm_bindgen]
pub fn caml_bn254_fq_of_string(s: String) -> Result<WasmBn254Fq, JsValue> {
    let biguint = BigUint::parse_bytes(s.as_bytes(), 10)
        .ok_or(JsValue::from_str("caml_bn254_fq_of_string"))?;

    match Fq::from_repr(bigint_256::of_biguint(&biguint)) {
        Some(x) => Ok(x.into()),
        None => Err(JsValue::from_str("caml_bn254_fq_of_string")),
    }
}

#[wasm_bindgen]
pub fn caml_bn254_fq_print(x: WasmBn254Fq) {
    println!("{}", bigint_256::to_biguint(&(x.0.into_repr())));
}

#[wasm_bindgen]
pub fn caml_bn254_fq_compare(x: WasmBn254Fq, y: WasmBn254Fq) -> i32 {
    match x.0.cmp(&y.0) {
        Less => -1,
        Equal => 0,
        Greater => 1,
    }
}

#[wasm_bindgen]
pub fn caml_bn254_fq_equal(x: WasmBn254Fq, y: WasmBn254Fq) -> bool {
    x.0 == y.0
}

#[wasm_bindgen]
pub fn caml_bn254_fq_random() -> WasmBn254Fq {
    WasmBn254Fq(UniformRand::rand(&mut rand::thread_rng()))
}

#[wasm_bindgen]
pub fn caml_bn254_fq_rng(i: i32) -> WasmBn254Fq {
    // We only care about entropy here, so we force a conversion i32 -> u32.
    let i: u64 = (i as u32).into();
    let mut rng: StdRng = rand::SeedableRng::seed_from_u64(i);
    WasmBn254Fq(UniformRand::rand(&mut rng))
}

#[wasm_bindgen]
pub fn caml_bn254_fq_to_bigint(x: WasmBn254Fq) -> WasmBigInteger256 {
    WasmBigInteger256(x.0.into_repr())
}

#[wasm_bindgen]
pub fn caml_bn254_fq_of_bigint(x: WasmBigInteger256) -> Result<WasmBn254Fq, JsValue> {
    match Fq::from_repr(x.0) {
        Some(x) => Ok(x.into()),
        None => Err(JsValue::from_str("caml_bn254_fq_of_bigint")),
    }
}

#[wasm_bindgen]
pub fn caml_bn254_fq_two_adic_root_of_unity() -> WasmBn254Fq {
    WasmBn254Fq(FftField::two_adic_root_of_unity())
}

#[wasm_bindgen]
pub fn caml_bn254_fq_domain_generator(log2_size: i32) -> WasmBn254Fq {
    match Domain::new(1 << log2_size) {
        Some(x) => WasmBn254Fq(x.group_gen),
        None => panic!("caml_bn254_fq_domain_generator"),
    }
}

#[wasm_bindgen]
pub fn caml_bn254_fq_to_bytes(x: WasmBn254Fq) -> Vec<u8> {
    let len = std::mem::size_of::<Fq>();
    let mut str: Vec<u8> = Vec::with_capacity(len);
    str.resize(len, 0);
    let str_as_fq: *mut Fq = str.as_mut_ptr().cast::<Fq>();
    unsafe {
        *str_as_fq = x.0;
    }
    str
}

#[wasm_bindgen]
pub fn caml_bn254_fq_of_bytes(x: &[u8]) -> WasmBn254Fq {
    let len = std::mem::size_of::<Fq>();
    if x.len() != len {
        panic!("caml_bn254_fq_of_bytes");
    };
    let x = unsafe { *(x.as_ptr() as *const Fq) };
    WasmBn254Fq(x)
}

#[wasm_bindgen]
pub fn caml_bn254_fq_deep_copy(x: WasmBn254Fq) -> WasmBn254Fq {
    x
}
