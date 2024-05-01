use crate::curve::{Curve, Point};


pub struct Setup {
    pub curve: Curve,
    //  ([1]₁, [x]₁, ..., [x^{d-1}]₁)
    //  = ( G,    xG,  ...,  x^{d-1}G ), where G is a generator of G_2
    // powers_of_x: list[G1Point]
    pub powers_of_x: Vec<Point>,

    // # [x]₂ = xH, where H is a generator of G_2
    pub X2: G2Point
}

impl Setup {
    // need polynomial type first
    fn commit(&self, values: Polynomial) -> Point {
        // Change to Lagrange Basise
        // Run inverse FFT to convert values from Lagrange basis to monomial basis
        // Optional: Check values size does not exceed maximum power setup can handle
        // Compute linear combination of setup with values
        todo!()
    }


    fn read_srs_from_file(&self) -> Setup {
        // Need to generate our own SRS
        // Read SRS from file
        // Parse SRS from file
        // Return SRS
        todo!()
    }

    fn verification_key(self, pk: CommonPreprocessedInput) -> VerificationKey{
        todo!()
    }
}