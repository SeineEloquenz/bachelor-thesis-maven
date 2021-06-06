package edu.kit.iti.formal.vser.converters;

final class Short_ {

    private Short_() {
        //Utility class
    }

    /*@ normal_behavior
      @
      @ ensures \result.length == 2;
      @ ensures value == (short) (((\result[0] & 0xFF) << 8) ^ (\result[1] & 0xFF));
      @*/
    static /*@pure@*/ byte[] toBytes(short value) {
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
    static /*@pure@*/ short fromBytes(byte[] bytes) {
        return (short) (((bytes[0] & 0xFF) << 8) ^ (bytes[1] & 0xFF));
    }
}
