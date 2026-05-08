; ModuleID = 'pointer_arith.bc'
source_filename = "pointer_arith.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 !dbg !10 {
  %1 = alloca i32, align 4
  %2 = alloca i32*, align 8
  store i32 0, i32* %1, align 4
  call void @llvm.dbg.declare(metadata i32** %2, metadata !13, metadata !DIExpression()), !dbg !14
  %3 = call noalias i8* @malloc(i64 12) #4, !dbg !15
  %4 = bitcast i8* %3 to i32*, !dbg !16
  store i32* %4, i32** %2, align 8, !dbg !14
  %5 = load i32*, i32** %2, align 8, !dbg !17
  %6 = getelementptr inbounds i32, i32* %5, i64 0, !dbg !17
  store i32 10, i32* %6, align 4, !dbg !18
  %7 = load i32*, i32** %2, align 8, !dbg !19
  %8 = getelementptr inbounds i32, i32* %7, i64 1, !dbg !19
  store i32 20, i32* %8, align 4, !dbg !20
  %9 = load i32*, i32** %2, align 8, !dbg !21
  %10 = getelementptr inbounds i32, i32* %9, i64 2, !dbg !21
  store i32 30, i32* %10, align 4, !dbg !22
  %11 = load i32*, i32** %2, align 8, !dbg !23
  %12 = getelementptr inbounds i32, i32* %11, i64 0, !dbg !23
  %13 = load i32, i32* %12, align 4, !dbg !23
  %14 = load i32*, i32** %2, align 8, !dbg !24
  %15 = getelementptr inbounds i32, i32* %14, i64 1, !dbg !24
  %16 = load i32, i32* %15, align 4, !dbg !24
  %17 = add nsw i32 %13, %16, !dbg !25
  %18 = load i32*, i32** %2, align 8, !dbg !26
  %19 = getelementptr inbounds i32, i32* %18, i64 2, !dbg !26
  %20 = load i32, i32* %19, align 4, !dbg !26
  %21 = add nsw i32 %17, %20, !dbg !27
  %22 = icmp eq i32 %21, 60, !dbg !28
  %23 = zext i1 %22 to i32, !dbg !28
  %24 = call i32 (i32, ...) bitcast (i32 (...)* @assert to i32 (i32, ...)*)(i32 %23), !dbg !29
  %25 = load i32*, i32** %2, align 8, !dbg !30
  %26 = bitcast i32* %25 to i8*, !dbg !30
  call void @free(i8* %26) #4, !dbg !31
  ret i32 0, !dbg !32
}

; Function Attrs: nofree nosync nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: nounwind
declare dso_local noalias i8* @malloc(i64) #2

declare dso_local i32 @assert(...) #3

; Function Attrs: nounwind
declare dso_local void @free(i8*) #2

attributes #0 = { noinline nounwind optnone uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nofree nosync nounwind readnone speculatable willreturn }
attributes #2 = { nounwind "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!6, !7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "Ubuntu clang version 12.0.1-++20211029101322+fed41342a82f-1~exp1~20211029221816.4", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, retainedTypes: !3, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "pointer_arith.c", directory: "/programs")
!2 = !{}
!3 = !{!4}
!4 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !5, size: 64)
!5 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!6 = !{i32 7, !"Dwarf Version", i32 4}
!7 = !{i32 2, !"Debug Info Version", i32 3}
!8 = !{i32 1, !"wchar_size", i32 4}
!9 = !{!"Ubuntu clang version 12.0.1-++20211029101322+fed41342a82f-1~exp1~20211029221816.4"}
!10 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 4, type: !11, scopeLine: 4, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!11 = !DISubroutineType(types: !12)
!12 = !{!5}
!13 = !DILocalVariable(name: "arr", scope: !10, file: !1, line: 5, type: !4)
!14 = !DILocation(line: 5, column: 8, scope: !10)
!15 = !DILocation(line: 5, column: 21, scope: !10)
!16 = !DILocation(line: 5, column: 14, scope: !10)
!17 = !DILocation(line: 6, column: 3, scope: !10)
!18 = !DILocation(line: 6, column: 10, scope: !10)
!19 = !DILocation(line: 7, column: 3, scope: !10)
!20 = !DILocation(line: 7, column: 10, scope: !10)
!21 = !DILocation(line: 8, column: 3, scope: !10)
!22 = !DILocation(line: 8, column: 10, scope: !10)
!23 = !DILocation(line: 9, column: 10, scope: !10)
!24 = !DILocation(line: 9, column: 19, scope: !10)
!25 = !DILocation(line: 9, column: 17, scope: !10)
!26 = !DILocation(line: 9, column: 28, scope: !10)
!27 = !DILocation(line: 9, column: 26, scope: !10)
!28 = !DILocation(line: 9, column: 35, scope: !10)
!29 = !DILocation(line: 9, column: 3, scope: !10)
!30 = !DILocation(line: 10, column: 8, scope: !10)
!31 = !DILocation(line: 10, column: 3, scope: !10)
!32 = !DILocation(line: 11, column: 3, scope: !10)
