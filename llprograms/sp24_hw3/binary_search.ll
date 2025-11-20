; binary search of an array
%arr = type [10 x i64]
@input_arr = global %arr [ i64 -13, i64 3, i64 5, i64 15, i64 17, i64 27, i64 28, i64 37, i64 45, i64 54]


define i64 @main(i64 %argc, i8** %argv) {
  %1 = getelementptr %arr, %arr* @input_arr, i64 0, i64 0
  %2 = call i64 @binary_search(i64* %1, i64 45, i64 0, i64 9)
  ret i64 %2
}

define i64 @binary_search(i64* %a, i64 %x, i64 %lo, i64 %hi) {
  ; return if hi < lo
  %1 = icmp slt i64 %hi, %lo
  br i1 %1, label %ret_base, label %loop

loop:
  ; find midpoint index in the array
  %2 = add i64 %lo, %hi
  %m = ashr i64 %2, 1

  ; find midpoint element
  %3 = getelementptr i64, i64* %a, i64 %m
  %e = load i64, i64* %3
  
  ; see if midpoint element is equal to x
  %4 = icmp eq i64 %e, %x
  br i1 %4, label %ret_found, label %divide

divide:
  ; see if x is less than midpoint elt
  %5 = icmp slt i64 %x, %e
  br i1 %5, label %is_less, label %is_greater

is_less: ; if x < arr[mid]
  %6 = sub i64 %m, 1
  %7 = call i64 @binary_search(i64* %a, i64 %x, i64 %lo, i64 %6)
  ret i64 %7
is_greater: ; if x > arr[mid]
  %8 = add i64 %m, 1
  %9 = call i64 @binary_search(i64* %a, i64 %x, i64 %8, i64 %hi)
  ret i64 %9

ret_base:
  ret i64 -1

ret_found:
  ret i64 %m
}
