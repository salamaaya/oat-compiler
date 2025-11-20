%array_t = type {[10 x i64]}

@array_g = global %array_t {[10 x i64] [i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0]}

define i1 @triangle(i64 %max) {
  %counter = alloca i64
  store i64 1, i64* %counter

  br label %loop
  
loop: 
  %current_counter = load i64, i64* %counter
  %last_counter = add i64 %current_counter, -1 
  %last_ptr = getelementptr %array_t, %array_t* @array_g, i64 %last_counter
  %last_val = load i64, i64* %last_ptr

  ; Store the triangle number in the array
  %current_val = add i64 %last_val, %current_counter
  %current_ptr = getelementptr %array_t, %array_t* @array_g, i64 %current_counter
  store i64 %current_val, i64* %current_ptr

  %correct_check = call i1 @check(i64 %current_val, i64 %current_counter)
  br i1 %correct_check, label %success, label %fail

success: 
  ; Increment the counter & store
  %next_counter = add i64 %current_counter, 1
  store i64 %next_counter, i64* %counter

  ; Check if the counter exceeds the size of the array
  %less_than_size = icmp slt i1 %next_counter, %max
  br i1 %less_than_size, label %loop, label %exit

exit:
  ret i1 0 

fail: 
  ret i1 1
}

define i1 @check(i64 %val, i64 %ind) {
  %t1 = add i64 %ind, 1
  %t3 = mul i64 %ind, %t1

  ; * 2 because no divide
  %val2 = mul i64 %val, 2
  %cmp = icmp eq i1 %val2, %t3
  br i1 %cmp, label %success, label %fail

fail:
  ret i1 0

success:
  ret i1 1
}

define i1 @main(i64 %argc, i8** %arcv) {
  %ret = call i1 @triangle(i64 10)
  %last_check = call i1 @check(i64 45, i64 9)
  %invert = sub i1 1, %last_check 
  %ret2 = add i64 %ret, %invert

  ret i1 %ret2
}
