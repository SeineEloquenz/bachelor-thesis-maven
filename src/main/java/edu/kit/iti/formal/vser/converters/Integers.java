package edu.kit.iti.formal.vser.converters;

import edu.kit.iti.formal.vser.utils.ArrayUtils;

public final class Integers {

    public static final int BYTE_SIZE = 4;

    private Integers() {
        //Utility class
    }

    /*@ public normal_behavior
      @
      @ ensures array.length * BYTE_SIZE == \result.length;
      @ ensures (\forall int k; 0 <= k && k < array.length; deserializeArray(\result)[k] == array[k]);
      @ ensures \fresh(\result);
      @ accessible array[*];
      @ assignable \nothing;
      @*/
    public static /*@pure@*/ byte[] serializeArray(int[] array) {
        final byte[] tmp = new byte[array.length * BYTE_SIZE];
        /*@
          @ maintaining 0 <= i && i <= array.length;
          @ maintaining (\forall int j; 0 <= j && j < i; deserialize(ArrayUtils.subArray(tmp, j * BYTE_SIZE, BYTE_SIZE)) == array[j]);
          @ assignable tmp[*];
          @ decreasing array.length - i;
          @*/
        for (int i = 0; i < array.length; i++) {
            ArrayUtils.putInto(tmp, serialize(array[i]), i * BYTE_SIZE);
        }
        return tmp;
    }

    /*@ public normal_behavior
      @
      @ requires bytes.length % BYTE_SIZE == 0;
      @
      @ ensures bytes.length / BYTE_SIZE == \result.length;
      @ ensures (\forall int i; 0 <= i && i < \result.length; deserialize(ArrayUtils.subArray(bytes, i * BYTE_SIZE, BYTE_SIZE)) == \result[i]);
      @ ensures \fresh(\result);
      @ accessible bytes[*];
      @ assignable \nothing;
      @*/
    public static /*@pure@*/ int[] deserializeArray(byte[] bytes) {
        int[] tmp = new int[bytes.length / BYTE_SIZE];
        /*@
          @ maintaining 0 <= i && i <= tmp.length;
          @ maintaining (\forall int j; 0 <= j && j < i; deserialize(ArrayUtils.subArray(bytes, j * BYTE_SIZE, BYTE_SIZE)) == tmp[j]);
          @ assignable tmp[*];
          @ decreasing tmp.length - i;
          @*/
        for (int i = 0; i < tmp.length; i++) {
            tmp[i] = deserialize(ArrayUtils.subArray(bytes, i * BYTE_SIZE, BYTE_SIZE));
        }
        return tmp;
    }

    /*@ public normal_behavior
      @
      @ ensures \result.length == BYTE_SIZE;    //(S1)
      @ ensures value == deserialize(\result);  //(S2)
      @ ensures \fresh(\result);                //(S3)
      @ assignable \nothing;
      @*/
    public static /*@pure@*/ byte[] serialize(int value) {
        return Integer_KeY.toBytes(value);
    }

    /*@ public normal_behavior
      @
      @ requires bytes.length == BYTE_SIZE;
      @ ensures \result == Integer_KeY.fromBytes(bytes);    //(D)
      @ assignable \strictly_nothing;
      @*/
    public static /*@strictly_pure@*/ int deserialize(byte[] bytes) {
        return Integer_KeY.fromBytes(bytes);
    }

    /*@ public normal_behavior
      @
      @ ensures \result == Integers.BYTE_SIZE + integers.length * BYTE_SIZE;
      @ assignable \strictly_nothing;
      @*/
    public static /*@strictly_pure@*/ int byteSize(int[] integers) {
        return Integers.BYTE_SIZE + integers.length * BYTE_SIZE;
    }
}
