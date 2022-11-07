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

#[test]
fn scalar32_set_int() {
    let digits: [u32; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
    let mut scalar: Scalar32 = Scalar32::new(digits);
    scalar.set_int(42);
    assert_eq!(scalar.d, [42, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn scalar32_get_bits() {
    let digits: [u32; 8] = [
        0b11000101101101101111111101101011,
        0b11101011011110101010001010101010,
        0b00101010111010100010101100101110,
        0b00010101111010101111100011010111,
        0b11101011011110101010001010101010,
        0b01111011110101011110000001010111,
        0b00001011110101111111111010110111,
        0b11110101000100110110100110101110,
    ];
    let scalar: Scalar32 = Scalar32::new(digits);

    assert_eq!(scalar.get_bits(33, 15).unwrap(), 0b101000101010101);
    // Tries to get a bit sequence from a two different digits.
    assert_eq!(scalar.get_bits(60, 8).unwrap(), 0b11101110);
    // Count is 0 : nonsense to get 0 bits.
    assert_eq!(
        scalar.get_bits(56, 0),
        Err(String::from("count must be in ]0, 32], got 0"))
    );
    // Count is > 32 : the sequence must fit a 32bits integer.
    assert_eq!(
        scalar.get_bits(33, 56),
        Err(String::from("count must be in ]0, 32], got 56"))
    );
    // Overflow : offset + count > 256.
    assert_eq!(
        scalar.get_bits(240, 20),
        Err(String::from("offset + count must be in [1, 256], got 260"))
    );
}

#[test]
fn scalar32_check_overflow() {
    let limbs: [u32; 8] = [
        N_0_32, N_1_32, N_2_32, N_3_32, N_4_32, N_5_32, N_6_32, N_7_32,
    ];
    let scalar: Scalar32 = Scalar32::new(limbs);
    // If the scalar is equal to the limbs, should return true.
    assert_eq!(scalar.check_overflow(), true);

    // If the scalar exceeds the limbs, should return 1.
    let mut overflowed_scalar: Scalar32 = scalar.clone();
    overflowed_scalar.d[0] += 1;
    assert_eq!(overflowed_scalar.check_overflow(), true);

    // If the scalar is less than the limbs, should return 0.
    let mut non_overflowed_scalar: Scalar32 = scalar.clone();
    non_overflowed_scalar.d[0] -= 1;
    assert_eq!(non_overflowed_scalar.check_overflow(), false);
}

#[test]
fn scalar32_reduce() {
    let limbs: [u32; 8] = [
        N_0_32, N_1_32, N_2_32, N_3_32, N_4_32, N_5_32, N_6_32, N_7_32,
    ];
    let mut scalar: Scalar32 = Scalar32::new(limbs);
    let mut overflowed_scalar: Scalar32 = scalar.clone();
    overflowed_scalar.d[0] += 42;
    let mut non_overflowed_scalar: Scalar32 = scalar.clone();
    non_overflowed_scalar.d[0] -= 42;
    scalar.reduce();
    overflowed_scalar.reduce();
    non_overflowed_scalar.reduce();

    // Checks the reducing of a scalar that equals the limbs.
    assert_eq!(scalar.d, [0, 0, 0, 0, 0, 0, 0, 0]);
    // Checks the reducing of a scalar that exceeds the limbs.
    assert_eq!(overflowed_scalar.d, [42, 0, 0, 0, 0, 0, 0, 0]);
    // Cehcks the reducing of a scalar that does not exceeds the limbs.
    assert_eq!(non_overflowed_scalar.d, [4294967254, 4294967295, 4294967295, 4294967295, 4294967295, 4294967295, 4294967295, 4294967295]);
}

// #[test]
// fn scalar32_add() {
//     const MIN: u32 = 0;
//     const MAX: u32 = 4294967295;
//     let min: [u32; 8] = [
//         MIN, MIN, MIN, MIN, MIN, MIN, MIN, MIN,
//     ];
//     let max: [u32; 8] = [
//         MAX, MAX, MAX, MAX, MAX, MAX, MAX, MAX,
//     ];
//     let limbs: [u32; 8] = [
//         N_0_32, N_1_32, N_2_32, N_3_32, N_4_32, N_5_32, N_6_32, N_7_32,
//     ];
//     let huge: [u32; 8] = [
//         2147483648, 0, 0, 0, 0, 0, 0, 0
//     ];
//     let scalar_min: Scalar32 = Scalar32::new(min);
//     let scalar_max: Scalar32 = Scalar32::new(max);
//     let scalar_limbs: Scalar32 = Scalar32::new(limbs);
//     let mut scalar_huge: Scalar32 = Scalar32::new(huge);
//     scalar_huge = scalar_huge.add(&scalar_huge).unwrap();
//     println!("{:?}", scalar_huge);
// }
