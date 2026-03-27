try {
    return fit(new Gaussian.Parametric(), guess);
} catch (NotStrictlyPositiveException e) {
    // if the initial guess gives NaN variance, try again with default guess
    guess[2] = 1; // setting the variance to 1
    return fit(new Gaussian.Parametric(), guess);
}