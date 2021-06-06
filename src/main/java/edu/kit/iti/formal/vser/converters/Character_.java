package edu.kit.iti.formal.vser.converters;

final class Character_ {

    private Character_() {
        //Utility class
    }

    /*@ normal_behavior
      @
      @ ensures \result.length == 2;
      @ ensures value == (char) (((\result[0] & 0xFF) << 8) ^ (\result[1] & 0xFF));
      @*/
    static /*@pure@*/ byte[] toBytes(char value) {
        byte[] result = new byte[2];
        result[0] = (byte) (value >> (8));
        result[1] = (byte) (value       );
        return result;
    }

    /*@ normal_behavior
      @
      @ requires bytes != null; //JJBMC does not assume all parameters to be non-null by default like KeY, so we need to specify the precondition explicitly
      @ requires bytes.length == 2;
      @*/
    static /*@pure@*/ char fromBytes(byte[] bytes) {
        return (char) (((bytes[0] & 0xFF) << 8) ^ (bytes[1] & 0xFF));
    }
}
