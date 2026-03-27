if (NodeUtil.hasFinally(n) && !n.getLastChild().isBlock()) {
      Node finallyBlock = n.getLastChild();
      tryMinimizeExits(finallyBlock, exitType, labelName);
    }