public class IsUnique {

  /*@ public normal_behavior
    @ ensures (\result <==> (\forall int a, b;
    @                                0 <= a && a < s.length &&
    @                                0 <= b && b < s.length &&
    @                                a != b; s[a] != s[b]));
    @*/
  public boolean isUnique(char[] s) {
    int N = s.length;
    boolean b = true;
    int i = 0;
    
    /*@ loop_invariant 0 <= i && i <= N;
      @ loop_invariant (b <==> (\forall int a, b;
      @                                 0 <= a && a < i &&
      @                                 0 <= b && b < i &&
      @                                 a != b; s[a] != s[b]));
      @ assignable \nothing;
      @ decreases N - i;
      @*/
    while (b && i != N) {
      int j = 0;
      
      /*@ loop_invariant 0 <= j && j <= i;
        @ loop_invariant (\forall int k; 0 <= k < j; s[k] != s[i]);
        @ assignable \nothing;
        @ decreases i - j;
        @*/
      while (j != i && s[j] != s[i]) {
        j = j + 1;
      }
      b = j == i;
      i = i + 1;
    }
    return b;
  }
}
