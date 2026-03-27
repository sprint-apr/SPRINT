return new Iterator<Chromosome>() {
    int index = 0;
    @Override
    public boolean hasNext() {
        return index < chromosomes.size();
    }
    @Override
    public Chromosome next() {
        if(hasNext()) {
            return chromosomes.get(index++);
        }
        throw new java.util.NoSuchElementException();
    }
};