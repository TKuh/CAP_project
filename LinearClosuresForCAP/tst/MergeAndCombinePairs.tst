gap> START_TEST("MergeAndCombinePairsTest.tst");
gap> LoadPackage( "LinearClosuresForCAP", false );;
gap> list1 := [ ["a", 1], ["b", 3], ["c", 4] ];;
gap> list2 := [ ["d", 2], ["e", 4], ["f", 5] ];;
gap> QQ := HomalgFieldOfRationals();;
gap> rows := CategoryOfRows( QQ );; # Could use any other category for testing
gap> COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZero( rows, list1, list2, 0 );
[ [ "a", 0, 1 ], [ 0, "d", 2 ], [ "b", 0, 3 ], [ "c", "e", 4 ], \
[ 0, "f", 5 ] 
 ]
gap> 
gap> list1 := [ ["a", 1], ["b", 3], ["c", 4] ];;
gap> list2 := [ ["d", 3], ["e", 4], ["f", 5] ];;
gap> COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZero( rows, list1, list2, 0 );
[ [ "a", 0, 1 ], [ "b", "d", 3 ], [ "c", "e", 4 ], [ 0, "f", 5 ]\
 ]
gap> list1 := [ ];;
gap> list2 := [ ["d", 2], ["e", 4], ["f", 5] ];;
gap> COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZero( rows, list1, list2, 0 );
[ [ 0, "d", 2 ], [ 0, "e", 4 ], [ 0, "f", 5 ] ]
gap> list1 := [ ["a", 1], ["b", 3], ["c", 4] ];;
gap> list2 := [ ];;
gap> COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZero( rows, list1, list2, 0 );
[ [ "a", 0, 1 ], [ "b", 0, 3 ], [ "c", 0, 4 ] ]
gap> list1 := [ ["b", 3] ];;
gap> list2 := [ ["d", 2], ["e", 4], ["f", 5] ];;
gap> COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZero( rows, list1, list2, 0 );
[ [ 0, "d", 2 ], [ "b", 0, 3 ], [ 0, "e", 4 ], [ 0, "f", 5 ] ]
gap> list1 := [ ["a", 1], ["b", 3], ["c", 4] ];;
gap> list2 := [ ["f", 5] ];;
gap> COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZero( rows, list1, list2, 0 );
[ [ "a", 0, 1 ], [ "b", 0, 3 ], [ "c", 0, 4 ], [ 0, "f", 5 ] ]
gap> list1 := [ ["a", 1], ["b", 3], ["c", 4] ];;
gap> list2 := [ ["d", 2], ["e", 4], ["f", 5] ];;
gap> list3 := [ ["g", 1], ["h", 2], ["i", 4] ];;
gap> COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairs( rows, [ list1, list2, list3 ] );
[ [ [ "a", "g" ], 1 ], [ [ "d", "h" ], 2 ], [ [ "b" ], 3 ], 
  [ [ "c", "e", "i" ], 4 ], [ [ "f" ], 5 ] ]
gap> list1 := [ ["a", 1], ["b", 3], ["c", 4] ];;
gap> list2 := [ ["d", 1], ["e", 3], ["f", 4] ];;
gap> list3 := [ ["g", 1], ["h", 3], ["i", 4] ];;
gap> COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairs( rows, [ list1, list2, list3 ] );
[ [ [ "a", "d", "g" ], 1 ], [ [ "b", "e", "h" ], 3 ], 
  [ [ "c", "f", "i" ], 4 ] ]
gap> list1 := [ [[ "a" ], 1], [[ "b" ], 3], [[ "c" ], 4] ];;
gap> list2 := [ [[ "d" ], 1], [[ "e" ], 3], [[ "f" ], 4] ];;
gap> COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZero( rows, list1, list2, 0 );
[ [ [ "a" ], [ "d" ], 1 ], [ [ "b" ], [ "e" ], 3 ], 
  [ [ "c" ], [ "f" ], 4 ] ]
gap> STOP_TEST([ "MergeAndCombinePairsTest.tst" ], 1);
