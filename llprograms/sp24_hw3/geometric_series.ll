; fdustin, geneliu
; generates a geometric series of 10 numbers given a base and a factor
%array = type [10 x i64]

@base = global i64 2
@factor = global i64 2
@answer = global %array [ i64 2, i64 4, i64 8, i64 16, i64 32, i64 64, i64 128, i64 256, i64 512, i64 1024 ]
@temp= global %array [ i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0 ]

define i64 @check_answer(%array* %expected, %array* %actual) {
    %curr_idx = alloca i64
    store i64 0, i64* %curr_idx
    br label %loop_check_cond

    loop_check_cond:
        %idx = load i64, i64* %curr_idx
        %cond_keep = icmp slt i64 %idx, 10
        br i1 %cond_keep, label %loop_check_body, label %loop_check_exit

    loop_check_body:
        %exp_ptr = getelementptr %array, %array* %expected, i32 0, i64 %idx
        %act_ptr = getelementptr %array, %array* %actual, i32 0, i64 %idx
        %exp_val = load i64, i64* %exp_ptr
        %act_val = load i64, i64* %act_ptr

        %cmp = icmp eq i64 %exp_val, %act_val

        %new_idx = add i64 %idx, 1
        store i64 %new_idx, i64* %curr_idx
        br i1 %cmp, label %loop_check_cond, label %loop_check_bad

    loop_check_bad:
        ret i64 0

    loop_check_exit:
        ret i64 1
}

define void @geometric_series(i64 %base, i64 %factor, %array* %arr) {
    %curr_idx = alloca i64
    store i64 0, i64* %curr_idx
    br label %loop_geo_cond

    loop_geo_cond:
        %idx = load i64, i64* %curr_idx
        %cond = icmp slt i64 %idx, 10
        br i1 %cond, label %loop_geo_body, label %loop_geo_exit

    loop_geo_body:
        %should_use_base_value = icmp eq i64 %idx, 0
        br i1 %should_use_base_value, label %use_base_value, label %use_array_value
        use_base_value:
            ; load the base value into the 1st element of the array
            %arr_index_zero = getelementptr %array, %array* %arr, i32 0, i64 0
            store i64 %base, i64* %arr_index_zero
            ; increment the counter
            %new_idx_of_base = add i64 %idx, 1
            store i64 %new_idx_of_base, i64* %curr_idx
            br label %loop_geo_cond

        use_array_value:
            ; use the previous value to calculate the next value
            %prev_idx = sub i64 %idx, 1
            %prev_value_ptr = getelementptr %array, %array* %arr, i32 0, i64 %prev_idx
            %prev_value = load i64, i64* %prev_value_ptr
            %new_value = mul i64 %prev_value, %factor

            ; store the new value into the array
            %new_value_ptr = getelementptr %array, %array* %arr, i32 0, i64 %idx
            store i64 %new_value, i64* %new_value_ptr

            ; increment the counter
            %new_idx_of_non_base = add i64 %idx, 1
            store i64 %new_idx_of_non_base, i64* %curr_idx
            br label %loop_geo_cond

    loop_geo_exit:
        ret void
}

define i64 @main() {
    %base_local = load i64, i64* @base
    %factor_local = load i64, i64* @factor
    call void @geometric_series(i64 %base_local, i64 %factor_local, %array* @temp)
    %res = call i64 @check_answer(%array* @answer, %array* @temp)

    ret i64 %res
}
