use secp256k1r::scalar::*;

#[test]
fn scalar32_new() {
    let digits: [u32; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
    let scalar: Scalar32 = Scalar32::new(digits);
    assert_eq!(scalar.d, [0, 1, 2, 3, 4, 5, 6, 7]);
}

#[test]
fn scalar32_clone() {
    let digits: [u32; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
    let scalar1: Scalar32 = Scalar32::new(digits);
    let scalar2: Scalar32 = scalar1.clone();
    assert_eq!(scalar1.d, scalar2.d);
}

#[test]
fn scalar32_clear() {
    let digits: [u32; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
    let mut scalar: Scalar32 = Scalar32::new(digits);
    scalar.clear();
    assert_eq!(scalar.d, [0, 0, 0, 0, 0, 0, 0, 0]);
}