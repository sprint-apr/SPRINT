ShapeList other = (ShapeList) obj;
if (other.size() != this.size()) {
    return false;
}
for (int i = 0; i < this.size(); i++) {
    if (!ShapeUtilities.equal(this.getShape(i), other.getShape(i))) {
        return false;
    }
}
return true;