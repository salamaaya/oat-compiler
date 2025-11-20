define i64 @m(i64 %x) {
  %ans = add i64 %x, 1
  ret i64 %ans
}

define i64 @apply(i64(i64)* %f) {
  %ans = call i64 %f(i64 34)
  ret i64 %ans
}

define i64 @main(i64 %argc, i8** %argv) {
  %ans = call i64 @apply(i64(i64)* @m)
  ret %ans
}
