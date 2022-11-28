use crate::{PC_1, PC_2};

/// Recovers key candidates from provided subkey

pub fn recover_key(subkey: &[Bit], subkey_index: u8, key: &mut [Bit]) {
    let mut cd_key: Vec<Bit> = vec![Bit::Unknown; 56];
    for (sk_index, sk_bit) in subkey.iter().enumerate() {
        let cd_index = PC_2[sk_index] - 1;
        cd_key[cd_index] = *sk_bit;
    }

    let (mut c, mut d) = split(cd_key);
    rot_right(subkey_index, &mut c);
    rot_right(subkey_index, &mut d);
    c.append(&mut d);

    for (bit_index, bit) in c.iter().enumerate() {
        let key_index = PC_1[bit_index] - 1;
        let existing = &mut key[key_index];

        // only overwrite if bit is unknown. raise error on conflict
        if let Bit::Unknown = existing {
            *existing = *bit;
        } else if let Bit::Unknown = bit {
        } else if existing != bit {
            panic!("Conflict {:?} {:?}", existing, bit);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Bit {
    One,
    Zero,
    Unknown,
}

pub fn to_bit_vec(input: u64, len: u8) -> Vec<Bit> {
    let mut output = vec![];
    for i in 0..len {
        output.insert(
            0,
            match (input >> i) & 1 {
                0 => Bit::Zero,
                1 => Bit::One,
                _ => panic!("Conversion error"),
            },
        );
    }
    output
}

fn split(mut input: Vec<Bit>) -> (Vec<Bit>, Vec<Bit>) {
    let mut left = vec![];
    for _ in 0..input.len() / 2 {
        left.push(input.remove(0));
    }
    (left, input)
}

fn rot_right(amount: u8, bits: &mut Vec<Bit>) {
    for _ in 0..amount {
        let bit = bits.pop().unwrap();
        bits.insert(0, bit);
    }
}

impl ToString for Bit {
    fn to_string(&self) -> String {
        match self {
            Bit::One => '1',
            Bit::Zero => '0',
            Bit::Unknown => '?',
        }
        .to_string()
    }
}

#[cfg(test)]
mod test {
    use crate::key_recovery::Bit;

    use super::{recover_key, to_bit_vec};

    #[test]
    fn full() {
        let k1 = to_bit_vec(0x6A834AAB6DF2, 48);
        let k2 = to_bit_vec(0xF312B1C77BF3, 48);

        let mut k = vec![Bit::Unknown; 64];
        recover_key(&k1, 1, &mut k);
        recover_key(&k2, 2, &mut k);

        assert_eq!(
            k,
            vec![
                Bit::Zero,
                Bit::One,
                Bit::Zero,
                Bit::Zero,
                Bit::Zero,
                Bit::One,
                Bit::One,
                Bit::Unknown,
                Bit::Zero,
                Bit::Zero,
                Bit::Zero,
                Bit::One,
                Bit::Zero,
                Bit::One,
                Bit::One,
                Bit::Unknown,
                Bit::Zero,
                Bit::One,
                Bit::Zero,
                Bit::One,
                Bit::One,
                Bit::One,
                Bit::One,
                Bit::Unknown,
                Bit::One,
                Bit::One,
                Bit::Zero,
                Bit::Zero,
                Bit::Zero,
                Bit::One,
                Bit::Zero,
                Bit::Unknown,
                Bit::One,
                Bit::One,
                Bit::Zero,
                Bit::One,
                Bit::One,
                Bit::Zero,
                Bit::One,
                Bit::Unknown,
                Bit::Zero,
                Bit::Zero,
                Bit::One,
                Bit::Zero,
                Bit::One,
                Bit::Zero,
                Bit::One,
                Bit::Unknown,
                Bit::One,
                Bit::Zero,
                Bit::One,
                Bit::One,
                Bit::One,
                Bit::Zero,
                Bit::One,
                Bit::Unknown,
                Bit::Zero,
                Bit::One,
                Bit::Zero,
                Bit::Zero,
                Bit::One,
                Bit::Zero,
                Bit::One,
                Bit::Unknown
            ]
        );
    }
}
