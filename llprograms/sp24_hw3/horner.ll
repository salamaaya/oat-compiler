%arr_t = type [4 x i64]

; coeff of the polynomial 
@coeff_arr = global %arr_t [i64 2, i64 -6, i64 2, i64 -1]

define i64 @horner(%arr_t* %poly, i64 %n, i64 %x)
{
    
    ; make a slot for the result, and set to 0
    %result_p = alloca i64
    store i64 0, i64* %result_p

    ; make a slot for the loop index, and set to 0
    %i_p = alloca i64
    store i64 0, i64* %i_p
    

    ; enter the loop
    br label %loop_bound

loop_bound:
    ; check that the index < n
    %check_i = load i64, i64* %i_p
    %bound_check = icmp slt i64 %check_i, %n
    br i1 %bound_check, label %calc, label %horner_done

calc:

    ; get poly[i]
    %use_i = load i64, i64* %i_p
    %poly_i_p = getelementptr %arr_t, %arr_t* %poly, i64 0, i64 %use_i
    %poly_i = load i64, i64* %poly_i_p

    ; next result = result*x + poly[i]
    %current_result = load i64, i64* %result_p
    %temp_0 = mul i64 %current_result, %x
    %next_result = add i64 %temp_0, %poly_i
    store i64 %next_result, i64* %result_p

    ; i += 1, and loop back
    %new_i = add i64 %use_i, 1
    store i64 %new_i, i64* %i_p
    br label %loop_bound

horner_done:
    ; return the final result
    %final_result = load i64, i64* %result_p
    ret i64 %final_result
}

define i64 @main(i64 %argc, i8** %argv){
    ; uses horners method to evaluate a polynomial of degree n
    ; at x using only n multiplications .

    ; Here we are evaluating the polynomial 2x^3 -6x^2 + 2x - 1 at 3
    ; and we expect to get -5.
    %main_result = call i64 @horner(%arr_t* @coeff_arr, i64 4, i64 3)
    ret i64 %main_result
}