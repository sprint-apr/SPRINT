if (rowDimension <= 0 || columnDimension <= 0) {
        throw new MatrixDimensionMismatchException(rowDimension, columnDimension, 0, 0);
    }
    if ((long) rowDimension * columnDimension > Integer.MAX_VALUE) {
        throw new NumberIsTooLargeException((long) rowDimension * columnDimension,
                                             Integer.MAX_VALUE, false);
    }