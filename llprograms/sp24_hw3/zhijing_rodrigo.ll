@matrixA = global [4 x i64] [i64 1, i64 2, i64 3, i64 4]
@matrixB = global [4 x i64] [i64 5, i64 6, i64 7, i64 8]

define i64 @multiply(i64 %a, i64 %b) {
  %mul = mul i64 %a, %b
  ret i64 %mul
}

define i64 @main() {
  %result = alloca i64
  store i64 0, i64* %result

  %i = alloca i64
  store i64 0, i64* %i
  br label %loop

loop:
  %iVal = load i64, i64* %i
  %cond = icmp slt i64 %iVal, 4
  br i1 %cond, label %body, label %end

body:
  %aElemPtr = getelementptr [4 x i64], [4 x i64]* @matrixA, i64 0, i64 %iVal
  %bElemPtr = getelementptr [4 x i64], [4 x i64]* @matrixB, i64 0, i64 %iVal
  %aElem = load i64, i64* %aElemPtr
  %bElem = load i64, i64* %bElemPtr
  %product = call i64 @multiply(i64 %aElem, i64 %bElem)

  %acc = load i64, i64* %result
  %newAcc = add i64 %acc, %product
  store i64 %newAcc, i64* %result

  %nextVal = add i64 %iVal, 1
  store i64 %nextVal, i64* %i
  br label %loop

end:
  %finalResult = load i64, i64* %result
  ret i64 %finalResult
}