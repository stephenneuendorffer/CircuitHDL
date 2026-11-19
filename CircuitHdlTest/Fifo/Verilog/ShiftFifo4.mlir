"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<input clk : i1, input rst : i1, input s_valid : i1, input s_data : i8, input m_ready : i1, output m_valid : i1, output m_data : i8, output s_ready : i1>, parameters = [], sym_name = "ShiftFifo4"}> ({
  ^bb0(%arg0: i1, %arg1: i1, %arg2: i1, %arg3: i8, %arg4: i1):
    %0 = "hw.constant"() <{value = true}> : () -> i1
    %1 = "hw.constant"() <{value = 3 : i3}> : () -> i3
    %2 = "hw.constant"() <{value = 2 : i3}> : () -> i3
    %3 = "hw.constant"() <{value = 1 : i3}> : () -> i3
    %4 = "hw.constant"() <{value = 0 : i2}> : () -> i2
    %5 = "hw.constant"() <{value = 0 : i8}> : () -> i8
    %6 = "hw.constant"() <{value = 0 : i3}> : () -> i3
    %7 = "hw.constant"() <{value = -4 : i3}> : () -> i3
    %8 = "comb.and"(%arg2, %14) : (i1, i1) -> i1
    %9 = "comb.and"(%16, %arg4) : (i1, i1) -> i1
    %10 = "comb.concat"(%4, %9) : (i2, i1) -> i3
    %11 = "comb.sub"(%41, %10) : (i3, i3) -> i3
    %12 = "comb.xor"(%arg1, %0) : (i1, i1) -> i1
    %13 = "comb.icmp"(%41, %7) <{predicate = 1 : i64}> : (i3, i3) -> i1
    %14 = "comb.and"(%12, %13) : (i1, i1) -> i1
    %15 = "comb.icmp"(%41, %6) <{predicate = 1 : i64}> : (i3, i3) -> i1
    %16 = "comb.and"(%12, %15) : (i1, i1) -> i1
    %17 = "comb.concat"(%4, %8) : (i2, i1) -> i3
    %18 = "comb.add"(%41, %17) : (i3, i3) -> i3
    %19 = "comb.sub"(%18, %10) : (i3, i3) -> i3
    %20 = "comb.icmp"(%11, %6) <{predicate = 0 : i64}> : (i3, i3) -> i1
    %21 = "comb.and"(%8, %20) : (i1, i1) -> i1
    %22 = "comb.mux"(%9, %43, %42) : (i1, i8, i8) -> i8
    %23 = "comb.mux"(%21, %arg3, %22) : (i1, i8, i8) -> i8
    %24 = "comb.icmp"(%11, %3) <{predicate = 0 : i64}> : (i3, i3) -> i1
    %25 = "comb.and"(%8, %24) : (i1, i1) -> i1
    %26 = "comb.mux"(%9, %44, %43) : (i1, i8, i8) -> i8
    %27 = "comb.mux"(%25, %arg3, %26) : (i1, i8, i8) -> i8
    %28 = "comb.icmp"(%11, %2) <{predicate = 0 : i64}> : (i3, i3) -> i1
    %29 = "comb.and"(%8, %28) : (i1, i1) -> i1
    %30 = "comb.mux"(%9, %45, %44) : (i1, i8, i8) -> i8
    %31 = "comb.mux"(%29, %arg3, %30) : (i1, i8, i8) -> i8
    %32 = "comb.icmp"(%11, %1) <{predicate = 0 : i64}> : (i3, i3) -> i1
    %33 = "comb.and"(%8, %32) : (i1, i1) -> i1
    %34 = "comb.mux"(%33, %arg3, %45) : (i1, i8, i8) -> i8
    %35 = "comb.mux"(%12, %19, %6) : (i1, i3, i3) -> i3
    %36 = "comb.mux"(%12, %23, %5) : (i1, i8, i8) -> i8
    %37 = "comb.mux"(%12, %27, %5) : (i1, i8, i8) -> i8
    %38 = "comb.mux"(%12, %31, %5) : (i1, i8, i8) -> i8
    %39 = "comb.mux"(%12, %34, %5) : (i1, i8, i8) -> i8
    %40 = "seq.to_clock"(%arg0) : (i1) -> !seq.clock
    %41 = "seq.firreg"(%35, %40) <{name = "count"}> : (i3, !seq.clock) -> i3
    %42 = "seq.firreg"(%36, %40) <{name = "r0"}> : (i8, !seq.clock) -> i8
    %43 = "seq.firreg"(%37, %40) <{name = "r1"}> : (i8, !seq.clock) -> i8
    %44 = "seq.firreg"(%38, %40) <{name = "r2"}> : (i8, !seq.clock) -> i8
    %45 = "seq.firreg"(%39, %40) <{name = "r3"}> : (i8, !seq.clock) -> i8
    "hw.output"(%16, %42, %14) : (i1, i8, i1) -> ()
  }) : () -> ()
}) : () -> ()

