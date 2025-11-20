declare i8* @ll_ltoa(i64)
declare void @ll_puts(i8*)

%arr = type [10 x i64]

@nums = global %arr [ i64 5, i64 1, i64 4, i64 2, i64 3, i64 6, i64 10, i64 9, i64 7, i64 8 ]

define void @iter(void(i64)* %f, %arr* %l) {
  %1 = alloca i64
  store i64 0, i64* %1
  br label %loop
loop:
  %i = load i64, i64* %1
  %valid = icmp slt i64 %i, 10
  br i1 %valid, label %body, label %post
body:
  %idx = load i64, i64* %1
  %p = getelementptr %arr, %arr* %l, i64 0, i64 %idx
  %n = load i64, i64* %p
  call void %f(i64 %n)
  %newidx = add i64 %idx, 1
  store i64 %newidx, i64* %1
  br label %loop
post:  
  ret void
}

define void @print(i64 %x) {
  %1 = call i8* @ll_ltoa(i64 %x)
  call void @ll_puts(i8* %1)
  ret void
}

define void @main(i64 %argc, i8** %arcv) {
  call void @iter(void(i64)* @print, %arr* @nums)
  ret void
}
