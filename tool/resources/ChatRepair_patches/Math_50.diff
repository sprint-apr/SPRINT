if (x == x1) {
    final double delta = FastMath.max(rtol * FastMath.abs(x1), atol);
    if (f1 > f0) {
        // Switch x0 with x1.
        double tmp = x0;
        x0 = x1 - delta;
        x1 = tmp;
        tmp = f0;
        f0 = f1;
        f1 = tmp;
    } else {
        // Reduce the bracketing interval by applying an Illinois 'step'.
        x0 = x1 - delta;
        f0 = computeObjectiveValue(x0);
    }
}