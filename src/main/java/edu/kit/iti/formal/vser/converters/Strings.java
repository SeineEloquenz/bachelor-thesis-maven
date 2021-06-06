package edu.kit.iti.formal.vser.converters;

public final class Strings {

    private /*@spec_public@*/ static final int BYTE_SIZE_CHAR = Characters.BYTE_SIZE;

    private Strings() {

    }

    /*@ public normal_behavior
      @
      @ ensures string.length() * BYTE_SIZE_CHAR == \result.length;
      @ ensures (\forall int k; 0 <= k && k < \dl_strContent(string).length; \dl_strContent(deserialize(\result))[k] == \dl_strContent(string)[k]);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
    public static /*@pure@*/ byte[] serialize(String string) {
        return Characters.serializeArray(stringToCharArray(string));
    }

    /*@ public normal_behavior
      @
      @ requires bytes.length % BYTE_SIZE_CHAR == 0;
      @
      @ ensures \result.length() * BYTE_SIZE_CHAR == bytes.length;
      @ ensures (\forall int i; 0 <= i && i < \dl_strContent(\result).length; Characters.deserialize(edu.kit.iti.formal.vser.utils.ArrayUtils.subArray(bytes, i * BYTE_SIZE_CHAR, BYTE_SIZE_CHAR)) == \dl_strContent(\result)[i]);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
    public static /*@pure@*/ String deserialize(byte[] bytes) {
        return charArrayToString(Characters.deserializeArray(bytes));
    }

    /*@ public normal_behavior //We assume this method to be correct
      @
      @ ensures string.length() == \result.length;
      @ ensures \dl_strContent(string) == \dl_array2seq(\result);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
    private static /*@pure@*/ char[] stringToCharArray(String string) {
        return string.toCharArray();
    }

    /*@ public normal_behavior //We assume this method to be correct
      @
      @ ensures chars.length == \result.length();
      @ ensures \dl_strContent(\result) == \dl_array2seq(chars);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
    private static /*@pure@*/ String charArrayToString(char[] chars) {
        return new String(chars);
    }

    /*@ public normal_behavior
      @
      @ ensures \result == Integers.BYTE_SIZE + string.length() * BYTE_SIZE_CHAR;
      @ assignable \strictly_nothing;
      @*/
    public static /*@strictly_pure@*/ int byteSize(String string) {
        return Integers.BYTE_SIZE + string.length() * BYTE_SIZE_CHAR;
    }
}
