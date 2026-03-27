if (nameNode.getFirstChild().getType() == Token.NAME &&
          "Math".equals(nameNode.getFirstChild().getString()) &&
          !OBJECT_METHODS_WITHOUT_SIDEEFFECTS.contains(nameNode.getLastChild().getString())) {
        return false;
}