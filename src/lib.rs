const IP: [usize; 64] = [
    58, 50, 42, 34, 26, 18, 10, 2, 60, 52, 44, 36, 28, 20, 12, 4, 62, 54, 46, 38, 30, 22, 14, 6,
    64, 56, 48, 40, 32, 24, 16, 8, 57, 49, 41, 33, 25, 17, 9, 1, 59, 51, 43, 35, 27, 19, 11, 3, 61,
    53, 45, 37, 29, 21, 13, 5, 63, 55, 47, 39, 31, 23, 15, 7,
];

const INV_IP: [usize; 64] = [
    40, 8, 48, 16, 56, 24, 64, 32, 39, 7, 47, 15, 55, 23, 63, 31, 38, 6, 46, 14, 54, 22, 62, 30,
    37, 5, 45, 13, 53, 21, 61, 29, 36, 4, 44, 12, 52, 20, 60, 28, 35, 3, 43, 11, 51, 19, 59, 27,
    34, 2, 42, 10, 50, 18, 58, 26, 33, 1, 41, 9, 49, 17, 57, 25,
];

const PC_1: [usize; 56] = [
    57, 49, 41, 33, 25, 17, 9, 1, 58, 50, 42, 34, 26, 18, 10, 2, 59, 51, 43, 35, 27, 19, 11, 3, 60,
    52, 44, 36, 63, 55, 47, 39, 31, 23, 15, 7, 62, 54, 46, 38, 30, 22, 14, 6, 61, 53, 45, 37, 29,
    21, 13, 5, 28, 20, 12, 4,
];

const PC_2: [usize; 48] = [
    14, 17, 11, 24, 1, 5, 3, 28, 15, 6, 21, 10, 23, 19, 12, 4, 26, 8, 16, 7, 27, 20, 13, 2, 41, 52,
    31, 37, 47, 55, 30, 40, 51, 45, 33, 48, 44, 49, 39, 56, 34, 53, 46, 42, 50, 36, 29, 32,
];

const E: [usize; 48] = [
    32, 1, 2, 3, 4, 5, 4, 5, 6, 7, 8, 9, 8, 9, 10, 11, 12, 13, 12, 13, 14, 15, 16, 17, 16, 17, 18,
    19, 20, 21, 20, 21, 22, 23, 24, 25, 24, 25, 26, 27, 28, 29, 28, 29, 30, 31, 32, 1,
];

const P: [usize; 32] = [
    16, 7, 20, 21, 29, 12, 28, 17, 1, 15, 23, 26, 5, 18, 31, 10, 2, 8, 24, 14, 32, 27, 3, 9, 19,
    13, 30, 6, 22, 11, 4, 25,
];

const S: [[[u8; 16]; 4]; 8] = [
    [
        [14, 4, 13, 1, 2, 15, 11, 8, 3, 10, 6, 12, 5, 9, 0, 7],
        [0, 15, 7, 4, 14, 2, 13, 1, 10, 6, 12, 11, 9, 5, 3, 8],
        [4, 1, 14, 8, 13, 6, 2, 11, 15, 12, 9, 7, 3, 10, 5, 0],
        [15, 12, 8, 2, 4, 9, 1, 7, 5, 11, 3, 14, 10, 0, 6, 13],
    ],
    [
        [15, 1, 8, 14, 6, 11, 3, 4, 9, 7, 2, 13, 12, 0, 5, 10],
        [3, 13, 4, 7, 15, 2, 8, 14, 12, 0, 1, 10, 6, 9, 11, 5],
        [0, 14, 7, 11, 10, 4, 13, 1, 5, 8, 12, 6, 9, 3, 2, 15],
        [13, 8, 10, 1, 3, 15, 4, 2, 11, 6, 7, 12, 0, 5, 15, 9],
    ],
    [
        [10, 0, 9, 14, 6, 3, 15, 5, 1, 13, 12, 7, 11, 4, 2, 8],
        [13, 7, 0, 9, 3, 4, 6, 10, 2, 8, 5, 14, 12, 11, 15, 1],
        [13, 6, 4, 9, 8, 15, 3, 0, 11, 1, 2, 12, 5, 10, 14, 7],
        [1, 10, 13, 0, 6, 9, 8, 7, 4, 15, 14, 3, 11, 5, 2, 12],
    ],
    [
        [7, 13, 14, 3, 0, 6, 9, 10, 1, 2, 8, 5, 11, 12, 4, 15],
        [13, 8, 11, 5, 6, 15, 0, 3, 4, 7, 2, 12, 1, 10, 14, 9],
        [10, 6, 9, 0, 12, 11, 7, 13, 15, 1, 3, 14, 5, 2, 8, 4],
        [3, 15, 0, 6, 10, 1, 13, 8, 9, 4, 5, 11, 12, 7, 2, 14],
    ],
    [
        [2, 12, 4, 1, 7, 10, 11, 6, 8, 5, 3, 15, 13, 0, 14, 9],
        [14, 11, 2, 12, 4, 7, 13, 1, 5, 0, 15, 10, 3, 9, 8, 6],
        [4, 2, 1, 11, 10, 13, 7, 8, 15, 9, 12, 5, 6, 3, 0, 14],
        [11, 8, 12, 7, 1, 14, 2, 13, 6, 15, 0, 9, 10, 4, 5, 3],
    ],
    [
        [12, 1, 10, 15, 9, 2, 6, 8, 0, 13, 3, 4, 14, 7, 5, 11],
        [10, 15, 4, 2, 7, 12, 9, 5, 6, 1, 13, 14, 0, 11, 3, 8],
        [9, 14, 15, 5, 2, 8, 12, 3, 7, 0, 4, 10, 1, 13, 11, 6],
        [4, 3, 2, 12, 9, 5, 15, 10, 11, 14, 1, 7, 6, 0, 8, 13],
    ],
    [
        [4, 11, 2, 14, 15, 0, 8, 13, 3, 12, 9, 7, 5, 10, 6, 1],
        [13, 0, 11, 7, 4, 9, 1, 10, 14, 3, 5, 12, 2, 15, 8, 6],
        [1, 4, 11, 13, 12, 3, 7, 14, 10, 15, 6, 8, 0, 5, 9, 2],
        [6, 11, 13, 8, 1, 4, 10, 7, 9, 5, 0, 15, 14, 2, 3, 12],
    ],
    [
        [13, 2, 8, 4, 6, 15, 11, 1, 10, 9, 3, 14, 5, 0, 12, 7],
        [1, 15, 13, 8, 10, 3, 7, 4, 12, 5, 6, 11, 0, 14, 9, 2],
        [7, 11, 4, 1, 9, 12, 14, 2, 0, 6, 10, 13, 15, 3, 5, 8],
        [2, 1, 14, 7, 4, 10, 8, 13, 15, 12, 9, 0, 3, 5, 6, 11],
    ],
];

const U28_MASK: u32 = 0b0000_1111_1111_1111_1111_1111_1111_1111;

type U4 = u8;
type U6 = u8;
type U28 = u32;
type U48 = u64;
type U56 = u64;

pub fn des_encrypt_block(x: u64, k: u64) -> u64 {
    des_operation(x, k, false)
}

pub fn des_decrypt_block(c: u64, k: u64) -> u64 {
    des_operation(c, k, true)
}

fn des_operation(x: u64, k: u64, decryption: bool) -> u64 {
    let subkeys = gen_subkeys(k, decryption);
    let x = input_permutate(x);
    let mut r = x as u32;
    let mut l = (x >> 32) as u32;

    for subkey in subkeys {
        (l, r) = feistel_round(l, r, subkey);
    }

    let out = ((r as u64) << 32) + l as u64;

    inverse_input_permutate(out)
}

fn gen_subkeys(key: u64, decryption: bool) -> [U48; 16] {
    let key: U56 = pc_1(key);
    let mut d = (key & U28_MASK as u64) as u32;
    let mut c = (key >> 28) as u32;

    let mut subkeys: [U48; 16] = [0; 16];
    for i in 0..16 {
        if decryption && i != 0 {
            if [1, 2, 9, 16].contains(&(i + 1)) {
                c = rotate_u28_right(c, 1);
                d = rotate_u28_right(d, 1);
            } else {
                c = rotate_u28_right(c, 2);
                d = rotate_u28_right(d, 2);
            }
        } else if !decryption {
            if [1, 2, 9, 16].contains(&(i + 1)) {
                c = rotate_u28_left(c, 1);
                d = rotate_u28_left(d, 1);
            } else {
                c = rotate_u28_left(c, 2);
                d = rotate_u28_left(d, 2);
            }
        }
        let subkey = ((c as u64) << 28) + d as u64; //reconstruct 56bit value from c and d
        subkeys[i] = pc_2(subkey);
    }
    subkeys
}

fn rotate_u28_left(mut input: U28, amount: u8) -> U28 {
    let to_rotate = input >> (28 - amount);

    input <<= amount;
    input += to_rotate;
    input &= U28_MASK;
    input
}

fn rotate_u28_right(mut input: U28, amount: u8) -> U28 {
    let rotate_mask = (1 << amount) - 1;
    let to_rotate = input & rotate_mask;

    input = (input & !rotate_mask) >> amount;
    input += to_rotate << (28 - amount);
    input
}

fn substitute(input: U48) -> u32 {
    let mut output = 0_u32;
    for i in 0..8 {
        //get the 6 bits for current s-box
        let input = ((input >> (6 * (7 - i))) & 0b111111) as u8;
        let out: u32 = subst_box(i, input) as _;
        output += out;
        if i != 7 {
            output <<= 4;
        }
    }
    output
}

fn f_func(r: u32, key: U48) -> u32 {
    let exp_r = expand(r);
    let xored = key ^ exp_r;
    let subst = substitute(xored);
    permutate(subst)
}

fn subst_box(s: usize, input: U6) -> U4 {
    // get x-index for s-box
    let x: usize = ((input >> 1) & 0b1111) as _;

    //get y-index for s-box
    let y: usize = (((input >> 4) & 0b10) + (input & 0b1)) as _;
    S[s][y][x]
}

fn feistel_round(l: u32, r: u32, key: U48) -> (u32, u32) {
    let f_out = f_func(r, key);
    (r, f_out ^ l)
}

macro_rules! bit_map {
    ($func:ident<$map:ident>($it:ident,$il:expr) -> $ot:ident) => {
        fn $func(input: $it) -> $ot {
            let mut output = 0 as $ot;
            // iterate left-to-right over map
            for (i, b) in $map.iter().enumerate() {
                //add input bit mapped by $map to output
                output += (input as $ot >> ($il - 1 - (b - 1))) & 1;

                //shift output left for next bit
                if i != $map.len() - 1 {
                    output <<= 1;
                }
            }
            output
        }
    };
}
bit_map!(expand<E>(u32, 32)->U48);
bit_map!(permutate<P>(u32, 32)->u32);
bit_map!(input_permutate<IP>(u64, 64)->u64);
bit_map!(inverse_input_permutate<INV_IP>(u64, 64)->u64);
bit_map!(pc_1<PC_1>(u64, 64)->U56);
bit_map!(pc_2<PC_2>(U56, 56)->U48);

#[cfg(test)]
mod test {
    use des::cipher::{BlockEncrypt, KeyInit};
    use generic_array::GenericArray;

    use crate::{
        des_decrypt_block, des_encrypt_block, rotate_u28_left, rotate_u28_right, subst_box,
        U28_MASK,
    };

    #[test]
    fn subst_box_output() {
        let samples = &[
            (0, 0b000000, 14),
            (0, 0b101100, 2),
            (1, 0b010100, 2),
            (1, 0b101010, 4),
            (2, 0b111101, 2),
            (2, 0b101000, 8),
            (3, 0b011000, 11),
            (3, 0b000111, 5),
            (4, 0b011010, 0),
            (4, 0b000111, 12),
            (5, 0b010111, 14),
            (5, 0b001000, 9),
            (6, 0b010011, 3),
            (6, 0b110111, 15),
            (7, 0b101001, 4),
            (7, 0b011001, 0),
        ];
        for sample in samples {
            assert_eq!(subst_box(sample.0, sample.1), sample.2);
        }
    }

    #[test]
    fn rotate_u28_1() {
        let a = 0b00001000_00000000_00000000_00000000_u32;
        let a_rot = 0b00000000_00000000_00000000_00000010_u32;
        assert_eq!(rotate_u28_left(a, 2), a_rot);
        assert_eq!(rotate_u28_left(U28_MASK, 2), U28_MASK);
    }

    #[test]
    fn rotate_u28_2() {
        let a = 0b00001000_00000000_00000000_00000000_u32;
        let a_rot = 0b00000000_00000000_00000000_00000001_u32;
        assert_eq!(rotate_u28_left(a, 1), a_rot);
    }

    #[test]
    fn rotate_u28_3() {
        let a = 0b00001000_00000000_00000000_00000000_u32;
        let a_rot = 0b00000000_00000000_00000000_00000010_u32;
        assert_eq!(rotate_u28_right(a_rot, 2), a);
    }

    #[test]
    fn rotate_u28_4() {
        let a = 0b00001000_00000000_00000000_00000000_u32;
        let a_rot = 0b00000000_00000000_00000000_00000001_u32;
        assert_eq!(rotate_u28_right(a_rot, 1), a);
    }

    #[test]
    fn encrypt() {
        let samples = &[
            (0x3132333435363738, 0x0000000000000000, 0x3d7595a98bff809d),
            (0xFFFFFFFFFFFFFF00, 0x486920576F726421, 0xe7d0dff7ff479bc7),
        ];

        for sample in samples {
            assert_eq!(des_encrypt_block(sample.1, sample.0), sample.2);
        }
    }

    #[test]
    fn full_enc_dec() {
        for _ in 0..10 {
            let key = rand::random::<u64>();
            let data = rand::random::<u64>();
            let enc = des_encrypt_block(data, key);
            assert_ne!(data, enc);
            let dec = des_decrypt_block(enc, key);
            assert_eq!(data, dec);
        }
    }

    #[test]
    fn compare_with_des_lib() {
        let key = rand::random::<u64>();
        let kb1 = key as u8;
        let kb2 = (key >> 8) as u8;
        let kb3 = (key >> 16) as u8;
        let kb4 = (key >> 24) as u8;
        let kb5 = (key >> 32) as u8;
        let kb6 = (key >> 40) as u8;
        let kb7 = (key >> 48) as u8;
        let kb8 = (key >> 56) as u8;

        let data = rand::random::<u64>();
        let db1 = data as u8;
        let db2 = (data >> 8) as u8;
        let db3 = (data >> 16) as u8;
        let db4 = (data >> 24) as u8;
        let db5 = (data >> 32) as u8;
        let db6 = (data >> 40) as u8;
        let db7 = (data >> 48) as u8;
        let db8 = (data >> 56) as u8;
        let des_slice = &mut [db8, db7, db6, db5, db4, db3, db2, db1];
        let des_data = GenericArray::from_mut_slice(des_slice);

        let des = des::Des::new(GenericArray::from_slice(&[
            kb8, kb7, kb6, kb5, kb4, kb3, kb2, kb1,
        ]));
        des.encrypt_block(des_data);

        let enc = des_encrypt_block(data, key);
        let eb1 = enc as u8;
        let eb2 = (enc >> 8) as u8;
        let eb3 = (enc >> 16) as u8;
        let eb4 = (enc >> 24) as u8;
        let eb5 = (enc >> 32) as u8;
        let eb6 = (enc >> 40) as u8;
        let eb7 = (enc >> 48) as u8;
        let eb8 = (enc >> 56) as u8;

        assert_eq!(eb8, des_data[0]);
        assert_eq!(eb7, des_data[1]);
        assert_eq!(eb6, des_data[2]);
        assert_eq!(eb5, des_data[3]);
        assert_eq!(eb4, des_data[4]);
        assert_eq!(eb3, des_data[5]);
        assert_eq!(eb2, des_data[6]);
        assert_eq!(eb1, des_data[7]);
    }
}
