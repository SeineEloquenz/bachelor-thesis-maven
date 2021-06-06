package edu.kit.iti.formal.vser.utils;

public final class ArrayUtils {

    private ArrayUtils() {
        //Utility class
    }

    /*@ public normal_behavior
      @
      @ ensures \result.length == first.length + second.length;
      @ ensures \dl_array2seq(\result) == \seq_concat(\dl_array2seq(first), \dl_array2seq(second));
      @ ensures (\forall int i; 0 <= i && i < first.length;     first[i]    == \result[i]);
      @ ensures (\forall int i; 0 <= i && i < second.length;    second[i]   == \result[i + first.length]);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @ accessible first[*], second[*];
      @*/
    public static /*@pure@*/ byte[] concatArrays(byte[] first, byte[] second) {
        byte[] result = copyArray(first, second.length);
        /*@
          @ maintaining 0 <= i && i <= second.length;
          @ maintaining (\forall int j; 0 <= j && j < first.length; first[j]   == result[j]);
          @ maintaining (\forall int j; 0 <= j && j < i; second[j]  == result[first.length + j]);
          @ decreasing second.length - i;
          @ assignable result[first.length..result.length];
          @*/
        for (int i = 0; i < second.length; i++) {
            result[first.length + i] = second[i];
        }
        return result;
    }

    /*@ public normal_behavior
      @
      @ ensures \result.length == first.length + second.length;
      @ ensures \dl_array2seq(\result) == \seq_concat(\dl_array2seq(first), \dl_array2seq(second));
      @ ensures (\forall int i; 0 <= i && i < first.length;     first[i]    == \result[i]);
      @ ensures (\forall int i; 0 <= i && i < second.length;    second[i]   == \result[i + first.length]);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @ accessible first[*], second[*];
      @*/
    public static /*@pure@*/ int[] concatArrays(int[] first, int[] second) {
        int[] result = copyArray(first, second.length);
        /*@
          @ maintaining 0 <= i && i <= second.length;
          @ maintaining (\forall int j; 0 <= j && j < first.length; first[j]   == result[j]);
          @ maintaining (\forall int j; 0 <= j && j < i; second[j]  == result[first.length + j]);
          @ decreasing second.length - i;
          @ assignable result[first.length..result.length];
          @*/
        for (int i = 0; i < second.length; i++) {
            result[first.length + i] = second[i];
        }
        return result;
    }

    /*@ public normal_behavior
      @
      @ ensures \result.length == array.length + 1;
      @ ensures \dl_array2seq(\result) == \seq_concat(\dl_array2seq(array), \seq_singleton(value));
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
    public static /*@pure@*/ byte[] concat(byte[] array, byte value) {
        final byte[] result = copyArray(array, 1);
        result[array.length] = value;
        return result;
    }

    /*@ public normal_behavior
      @
      @ requires additionalLength >= 0;
      @
      @ ensures \result.length == array.length + additionalLength;
      @ ensures (\forall int i; 0 <= i && i < array.length; \result[i] == array[i]);
      @ ensures \fresh(\result);
      @ accessible array[*], additionalLength;
      @ assignable \nothing;
      @*/
    public static /*@pure@*/ int[] copyArray(int[] array, int additionalLength) {
        final int[] res = new int[array.length + additionalLength];
        /*@
          @ maintaining 0 <= i && i <= array.length;
          @ maintaining (\forall int j; 0 <= j && j < i; res[j] == array[j]);
          @ decreasing array.length - i;
          @ assignable res[*];
          @*/
        for (int i = 0; i < array.length; i++) {
            res[i] = array[i];
        }
        return res;
    }

    /*@ public normal_behavior
      @
      @ requires additionalLength >= 0;
      @
      @ ensures \result.length == array.length + additionalLength;
      @ ensures (\forall int i; 0 <= i && i < array.length; \result[i] == array[i]);
      @ ensures \fresh(\result);
      @ accessible array[*], additionalLength;
      @ assignable \nothing;
      @*/
    public static /*@pure@*/ byte[] copyArray(byte[] array, int additionalLength) {
        final byte[] res = new byte[array.length + additionalLength];
        /*@
          @ maintaining 0 <= i && i <= array.length;
          @ maintaining (\forall int j; 0 <= j && j < i; res[j] == array[j]);
          @ decreasing array.length - i;
          @ assignable res[*];
          @*/
        for (int i = 0; i < array.length; i++) {
            res[i] = array[i];
        }
        return res;
    }

    /*@ public normal_behavior
      @
      @ requires 0 <= length;
      @ requires 0 <= beginIndex;
      @ requires beginIndex + length <= array.length;
      @
      @ ensures \result.length == length;
      @ ensures (\forall int i; 0 <= i && i < length; \result[i] == array[beginIndex + i]);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @ accessible array[beginIndex..beginIndex+length-1];
      @*/
    public static /*@pure@*/ byte[] subArray(byte[] array, int beginIndex, int length) {
        final byte[] res = new byte[length];
        /*@
          @ maintaining 0 <= i && i <= length;
          @ maintaining (\forall int j; 0 <= j && j < i; res[j] == array[beginIndex + j]);
          @ decreasing length - i;
          @ assignable res[*];
          @*/
        for (int i = 0; i < length; i++) {
            res[i] = array[beginIndex + i];
        }
        return res;
    }

    /*@ public normal_behavior
      @
      @ requires 0 <= length;
      @ requires 0 <= beginIndex;
      @ requires beginIndex + length <= array.length;
      @
      @ ensures \result.length == length;
      @ ensures (\forall int i; 0 <= i && i < length; \result[i] == array[beginIndex + i]);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @ accessible array[beginIndex..beginIndex+length-1];
      @*/
    public static /*@pure@*/ int[] subArray(int[] array, int beginIndex, int length) {
        final int[] res = new int[length];
        /*@
          @ maintaining 0 <= i && i <= length;
          @ maintaining (\forall int j; 0 <= j && j < i; res[j] == array[beginIndex + j]);
          @ decreasing length - i;
          @ assignable res[*];
          @*/
        for (int i = 0; i < length; i++) {
            res[i] = array[beginIndex + i];
        }
        return res;
    }

    /*@ public normal_behavior
      @
      @ requires 0 <= beginIndex;
      @ requires beginIndex + toPut.length <= array.length;
      @
      @ ensures array.length == \old(array.length);
      @ ensures (\forall int i; 0 <= i && i < toPut.length; array[beginIndex + i] == toPut[i]);
      @ assignable array[beginIndex..beginIndex+toPut.length-1];
      @*/
    public static void putInto(byte[] array, byte[] toPut,  int beginIndex) {
        /*@
          @ maintaining 0 <= i && i <= toPut.length;
          @ maintaining (\forall int j; 0 <= j && j < array.length && !( beginIndex <= j && j <= beginIndex + toPut.length); array[j] == \old(array[j]));
          @ maintaining (\forall int j; 0 <= j && j < i; array[beginIndex + j] == toPut[j]);
          @ decreasing toPut.length - i;
          @ assignable array[beginIndex..(beginIndex + toPut.length-1)];
          @*/
        for (int i = 0; i < toPut.length; i++) {
            array[beginIndex + i] = toPut[i];
        }
    }

    /*@ public normal_behavior
      @
      @ ensures \result <==> first.length == second.length && (\forall int i; 0 <= i && i < first.length; first[i] == second[i]);
      @ assignable \strictly_nothing;
      @*/
    public static /*@strictly_pure@*/ boolean equals(byte[] first, byte[] second) {
        if (first.length != second.length) {
            return false;
        }
        boolean same = true;
        /*@
          @ maintaining 0 <= i && i <= first.length;
          @ maintaining same <==> (\forall int j; 0 <= j && j < i; first[j] == second[j]);
          @ decreasing first.length - i;
          @ assignable \strictly_nothing;
          @*/
        for (int i = 0; i < first.length; i++) {
            same = same && first[i] == second[i];
        }
        return same;
    }

    /*@ public normal_behavior
      @
      @ ensures \result <==> first.length == second.length && (\forall int i; 0 <= i && i < first.length; first[i] == second[i]);
      @ assignable \strictly_nothing;
      @*/
    public static /*@strictly_pure@*/ boolean equals(short[] first, short[] second) {
        if (first.length != second.length) {
            return false;
        }
        boolean same = true;
        /*@
          @ maintaining 0 <= i && i <= first.length;
          @ maintaining same <==> (\forall int j; 0 <= j && j < i; first[j] == second[j]);
          @ decreasing first.length - i;
          @ assignable \strictly_nothing;
          @*/
        for (int i = 0; i < first.length; i++) {
            same = same && first[i] == second[i];
        }
        return same;
    }

    /*@ public normal_behavior
      @
      @ ensures \result <==> first.length == second.length && (\forall int i; 0 <= i && i < first.length; first[i] == second[i]);
      @ assignable \strictly_nothing;
      @*/
    public static /*@strictly_pure@*/ boolean equals(char[] first, char[] second) {
        if (first.length != second.length) {
            return false;
        }
        boolean same = true;
        /*@
          @ maintaining 0 <= i && i <= first.length;
          @ maintaining same <==> (\forall int j; 0 <= j && j < i; first[j] == second[j]);
          @ decreasing first.length - i;
          @ assignable \strictly_nothing;
          @*/
        for (int i = 0; i < first.length; i++) {
            same = same && first[i] == second[i];
        }
        return same;
    }

    /*@ public normal_behavior
      @
      @ ensures \result <==> first.length == second.length && (\forall int i; 0 <= i && i < first.length; first[i] == second[i]);
      @ assignable \strictly_nothing;
      @*/
    public static /*@strictly_pure@*/ boolean equals(int[] first, int[] second) {
        if (first.length != second.length) {
            return false;
        }
        boolean same = true;
        /*@
          @ maintaining 0 <= i && i <= first.length;
          @ maintaining same <==> (\forall int j; 0 <= j && j < i; first[j] == second[j]);
          @ decreasing first.length - i;
          @ assignable \strictly_nothing;
          @*/
        for (int i = 0; i < first.length; i++) {
            same = same && first[i] == second[i];
        }
        return same;
    }

    /*@ public normal_behavior
      @
      @ ensures \result <==> first.length == second.length && (\forall int i; 0 <= i && i < first.length; first[i] == second[i]);
      @ assignable \strictly_nothing;
      @*/
    public static /*@strictly_pure@*/ boolean equals(long[] first, long[] second) {
        if (first.length != second.length) {
            return false;
        }
        boolean same = true;
        /*@
          @ maintaining 0 <= i && i <= first.length;
          @ maintaining same <==> (\forall int j; 0 <= j && j < i; first[j] == second[j]);
          @ decreasing first.length - i;
          @ assignable \strictly_nothing;
          @*/
        for (int i = 0; i < first.length; i++) {
            same = same && first[i] == second[i];
        }
        return same;
    }

    /*@ public normal_behavior
      @
      @ ensures \result <==> first.length == second.length && (\forall int i; 0 <= i && i < first.length; first[i] == second[i]);
      @ assignable \strictly_nothing;
      @*/
    public static /*@strictly_pure@*/ boolean equals(boolean[] first, boolean[] second) {
        if (first.length != second.length) {
            return false;
        }
        boolean same = true;
        /*@
          @ maintaining 0 <= i && i <= first.length;
          @ maintaining same <==> (\forall int j; 0 <= j && j < i; first[j] == second[j]);
          @ decreasing first.length - i;
          @ assignable \strictly_nothing;
          @*/
        for (int i = 0; i < first.length; i++) {
            same = same && first[i] == second[i];
        }
        return same;
    }
}
