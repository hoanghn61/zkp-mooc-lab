pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 * This is functionally equivalent to `if (cond) { out = L; } else { out = R; }`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === in;
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 * Assumes `n` bit inputs. The behavior is not well-defined if any input is more than `n`-bits long.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */

template CheckBitLength(b) {
    assert(b < 254);
    signal input in;
    signal output out;
    signal aux;

    component iZ = IsZero();

    aux <-- (in >> b);
    iZ.in <== aux; 
    
    out <== iZ.out;
}


/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * elte, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);

    // choose the right checks based on `is_e_zero`
    component if_elte = IfThenElse();
    if_elte.cond <== is_e_zero.out;
    if_elte.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_elte.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_elte.out === 1;
}

/*
 * Right-shifts `b`-bit long `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(b, shift) {
    assert(shift < b);

    signal input x;
    signal output y;

    component x_bits = Num2Bits(b);
    x_bits.in <== x;

    signal y_bits[ b - shift ];
    for (var i = 0; i < b - shift; i++) {
        y_bits[i] <== x_bits.bits[i + shift];
    }

    component y_num = Bits2Num(b - shift);
    y_num.bits <== y_bits;

    y <== y_num.out;
}


/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    //// Although m_prime is P+1 bits long in no overflow case, it can be P+2 bits long
    //// in the overflow case and the constraints should not fail in either case
    component right_shift = RightShift(P+2, round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_elte[2];
    for (var i = 0; i < 2; i++) {
        if_elte[i] = IfThenElse();
        if_elte[i].cond <== no_overflow;
    }
    if_elte[0].L <== e_out_1;
    if_elte[0].R <== e_out_2;
    if_elte[1].L <== m_out_1;
    if_elte[1].R <== m_out_2;
    e_out <== if_elte[0].out;
    m_out <== if_elte[1].out;
}

/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
template LeftShift(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;

    assert(shift >= 0 || skip_checks);
    assert(shift < shift_bound || skip_checks);

    skip_checks * (1 - skip_checks) === 0;

    signal accumulator[shift_bound + 1];
    signal tripwire[shift_bound + 1];
    component equal_check[shift_bound];

    accumulator[0] <== x;
    tripwire[0] <== 1;

    for (var i = 0; i < shift_bound; i++) {
        // Check if current `i` is equal to `shift`
        equal_check[i] = IsEqual();
        equal_check[i].in[0] <== shift;
        equal_check[i].in[1] <== i;

        // Set tripwire to zero after the shift point is reached
        tripwire[i + 1] <== tripwire[i] * (1 - equal_check[i].out);
        accumulator[i + 1] <== accumulator[i] * (1 + tripwire[i + 1]);
    }

    y <== accumulator[shift_bound];
}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template MSNZB(b) {
    signal input in;
    signal input skip_checks;
    signal output one_hot[b];

    // Assert that if the check is not being skipped, `in` is positive and non-zero
    assert(skip_checks || in > 0);

    // Ensure skip_checks is a binary value
    skip_checks * (1 - skip_checks) === 0;

    // Extract a boolean value (lt.out) that represents whether 0 is less than `in` (i.e. `in` >= 0)
    component lt = LessThan(b);
    lt.in[0] <== 0;
    lt.in[1] <== in;

    // Assert `in` >= 0 by constraining (1 - lt.out) to be zero.
    // Note that we add the binary indicator `skip_checks` to the constraint to allow the constraint to be skipped.
    0 === (1 - lt.out) * (1 - skip_checks);

    // Convert b to bits to begin the MSNZB operation
    component num_bits = Num2Bits(b);
    num_bits.in <== in;

    // We set a comparator that compares the ith bit of `in` with the (i+1)th bit of an accumulattrip.
    // The accumulator serves as a tripwire that is set to 1 for all remaining values when the MSNZB is found.
    component comparator[b];
    signal accumulator[b+1];
    accumulator[b] <== 0;
    
    // Iterate through the bits of `in` from MSB to ltB.
    for (var i = b - 1; i >= 0; i--) {
        comparator[i] = OR();
        comparator[i].a <== num_bits.bits[i];
        comparator[i].b <== accumulator[i+1];

        // If the MSNZB has been found, this will always set to 1.
        accumulator[i] <== comparator[i].out;
    }

    // At this point, our accumulator has accumulated an array of bits that are 1's up to the MSNZB and 0's after.
    // Since our input is non-zero, we can assume that `accumulator` is not an array of all zeroes.
    for (var i = 0; i < b; i++) {
        one_hot[i] <== accumulator[i] - accumulator[i+1];
    }
}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template Normalize(k, p, P) {
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // Pull MSNZB of `m`. Since we already check validity of skip_checksin the MSNZB template, we can directly pass it in as a constraint.
    component msnzb = MSNZB(P+1);
    msnzb.in <== m;
    msnzb.skip_checks <== skip_checks;
    

    // We set array lengths to P+2 to make space for the final carry bit.
    signal mantissa_accumulator[P+2];
    signal reverse_accumulator[P+2];

    // Initialize accumulator values.
    mantissa_accumulator[P+1] <== m;
    reverse_accumulator[P+1] <== 1;

    var precision_offset = P;
    for (var i = P; i >= 0; i--) {
        // Carries the 1 over until it hits the MSNZB. Sets remaining values to 0.
        reverse_accumulator[i] <== (1 - msnzb.one_hot[i]) * reverse_accumulator[i + 1];

        // Accumulate mantissa value until MSNZB, after which we carry the final value to index 0.
        mantissa_accumulator[i] <== reverse_accumulator[i] * mantissa_accumulator[i + 1] + mantissa_accumulator[i + 1];

        // Reduce precision offset for each bit leading up to MSNZB.
        precision_offset -= reverse_accumulator[i];
    }

    // Set final exponent and mantissa values.
    m_out <== mantissa_accumulator[0];
    e_out <== e + precision_offset - p;
}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.
 */
template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;

    // Check that inputs are well-formed.
    component is_well_formed[2];
    for (var i = 0; i < 2; i++) {
        is_well_formed[i] = CheckWellFormedness(k, p);
        is_well_formed[i].e <== e[i];
        is_well_formed[i].m <== m[i];
    }

    // 
    signal e_left[2][p + 2];
    signal magnitude[2];

    // 
    for (var i = 0; i < 2; i++) {
        e_left[i][0] <== e[i];
        for(var j = 0; j < p+1; j++) {
            e_left[i][j+1] <== e_left[i][j]*2;
        }
        magnitude[i] <== e_left[i][p+1] + m[i];
    }

    component lt;
    lt = LessThan((2 * p) + 2);
    lt.in[0] <== magnitude[0];
    lt.in[1] <== magnitude[1];
    
 
    component switcher[2];
    signal alpha_e, alpha_m, beta_e, beta_m;
    
    // First switcher
    switcher[0] = Switcher();
    switcher[0].sel <== lt.out;
    switcher[0].L <== e[0];
    switcher[0].R <== e[1];
    alpha_e <== switcher[0].outL;
    beta_e <== switcher[0].outR;

    // Second switcher
    switcher[1] = Switcher();
    switcher[1].sel <== lt.out;
    switcher[1].L <== m[0];
    switcher[1].R <== m[1];
    alpha_m <== switcher[1].outL;
    beta_m <== switcher[1].outR;

    signal diff <== alpha_e - beta_e;

    signal m0;
    signal e0;
    signal m1;
    signal e1;
    signal m2;
    signal e2;

    // Bool for if precision + 1 is less than diff
    component ltp = LessThan(p);
    ltp.in[0] <== p + 1;
    ltp.in[1] <== diff;

    // Bool for if alpha_m is zero
    component is_zero = IsZero();
    is_zero.in <== alpha_e;

    // Trips if either precision is less than diff or alpha_e is zero
    component trip = OR();
    trip.a <== ltp.out;
    trip.b <== is_zero.out;

    component leftshift = LeftShift(p+2);
    leftshift.x <== alpha_m;
    leftshift.shift <== diff;
    leftshift.skip_checks <== trip.out;

    m0 <== leftshift.y + beta_m;
    e0 <== beta_e;

    component normalize = Normalize(k, p, 2 * p+1);
    normalize.e <== e0*(1 - trip.out);
    normalize.m <== m0*(1 - trip.out);
    normalize.skip_checks <== trip.out;
    e1 <== normalize.e_out;
    m1 <== normalize.m_out;

    component round_and_check = RoundAndCheck(k, p, 2 * p+1);
    round_and_check.e <== e1*(1-trip.out);
    round_and_check.m <== m1*(1-trip.out);
    e2 <== round_and_check.e_out;
    m2 <== round_and_check.m_out;

    component if_e = IfThenElse();
    if_e.cond <== trip.out;
    if_e.L <== alpha_e;
    if_e.R <== e2;
    e_out <== if_e.out;

    component if_m = IfThenElse();
    if_m.cond <== trip.out;
    if_m.L <== alpha_m;
    if_m.R <== m2;
    m_out <== if_m.out;
}