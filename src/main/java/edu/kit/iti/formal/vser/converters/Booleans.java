package edu.kit.iti.formal.vser.converters;

public final class Booleans {

    public  static final int BYTE_SIZE = 1;

    private Booleans() {
        //Utility class
    }

    /*@ private normal_behavior
      @ ensures (\forall int k; 0 <= k && k < bool.length; \result[k] == bool[k]);
      @*/
    private static boolean[] verifyBoolSer(boolean[] bool) {
        return deserializeArray(serializeArray(bool));
    }

    /*@ public normal_behavior
      @
      @ ensures array.length == \result.length;
      @ ensures (\forall int k; 0 <= k && k < array.length; deserialize(\result[k]) == array[k]);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
    public static /*@pure@*/ byte[] serializeArray(boolean[] array) {
        final byte[] tmp = new byte[array.length];
        /*@
          @ maintaining 0 <= i && i <= array.length;
          @ maintaining (\forall int j; 0 <= j && j < i; deserialize(tmp[j]) == array[j]);
          @ assignable tmp[*];
          @ decreasing array.length - i;
          @*/
        for (int i = 0; i < array.length; i++) {
            tmp[i] = serialize(array[i]);
        }
        return tmp;
    }

    /*@ public normal_behavior
      @
      @ ensures bytes.length == \result.length;
      @ ensures (\forall int i; 0 <= i && i < \result.length; deserialize(bytes[i]) == \result[i]);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
    public static /*@pure@*/ boolean[] deserializeArray(byte[] bytes) {
        boolean[] tmp = new boolean[bytes.length];
        /*@
          @ maintaining 0 <= i && i <= bytes.length;
          @ maintaining (\forall int j; 0 <= j && j < i; deserialize(bytes[j]) == tmp[j]);
          @ assignable tmp[*];
          @ decreasing bytes.length - i;
          @*/
        for (int i = 0; i < bytes.length; i++) {
            tmp[i] = deserialize(bytes[i]);
        }
        return tmp;
    }

    /*@ public normal_behavior
      @
      @ ensures deserialize(\result) == bool;
      @ ensures bool <==> \result == 1;
      @ assignable \strictly_nothing;
      @*/
    public static /*@strictly_pure@*/ byte serialize(boolean bool) {
        if (bool) {
            return 1;
        } else {
            return 0;
        }
    }

    /*@ public normal_behavior
      @
      @ ensures \result <==> (boolRepr == 1);
      @ assignable \strictly_nothing;
      @*/
    public static /*@strictly_pure@*/ boolean deserialize(byte boolRepr) {
        return boolRepr == 1;
    }

    /*@ public normal_behavior
      @
      @ assignable \strictly_nothing;
      @*/
    public static /*@strictly_pure@*/ int byteSize(boolean[] booleans) {
        return Integers.BYTE_SIZE + booleans.length;
    }
}
