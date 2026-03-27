if (entityValue >= 0 && entityValue <= 0x10FFFF) {
    char[] chars = Character.toChars(entityValue);
    out.write(chars);
    return 2 + (end - start) + (isHex ? 1 : 0) + 1;
}