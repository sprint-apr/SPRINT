if (searchStr.length() == 0) {
   return true;
}
if (str.length() < searchStr.length()) {
   return false;
}
final int length = searchStr.length();
for (int i = str.length() - length; i >= 0; i--) {
   if (str.regionMatches(true, i, searchStr, 0, length)) {
      return true;
   }
}
return false;