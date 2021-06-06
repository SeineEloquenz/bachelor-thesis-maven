package edu.kit.iti.formal.vser.converters;

final class Integer_ {

    private Integer_() {
        //Utility class
    }

    /*@ normal_behavior
      @
      @ ensures \result.length == 4;
      @ ensures value == (((\result[0] & 0xFF) << 24) ^ ((\result[1] & 0xFF) << 16) ^ ((\result[2] & 0xFF) << 8) ^ (\result[3] & 0xFF));
      @*/
    static /*@pure@*/ byte[] toBytes(int value) {
        byte[] result = new byte[4];
        result[0] = (byte) (value >> (24)   );
        result[1] = (byte) (value >> (16)   );
        result[2] = (byte) (value >> (8)    );
        result[3] = (byte) (value           );
        return result;
    }

    /*@ normal_behavior
      @
      @ requires bytes != null; //JJBMC does not assume all parameters to be non-null by default like KeY, so we need to specify the precondition explicitly
      @ requires bytes.length == 4;
      @ ensures (byte) (\result >> (24)   ) == bytes[0];
      @ ensures (byte) (\result >> (16)   ) == bytes[1];
      @ ensures (byte) (\result >> (8)    ) == bytes[2];
      @ ensures (byte) (\result           ) == bytes[3];
      @*/
    static /*@pure@*/ int fromBytes(byte[] bytes) {
        return ((bytes[0] & 0xFF) << 24) ^ ((bytes[1] & 0xFF) << 16) ^ ((bytes[2] & 0xFF) << 8) ^ (bytes[3] & 0xFF);
    }
}
