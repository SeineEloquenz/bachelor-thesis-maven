package edu.kit.iti.formal.vser.converters;

final class Long_KeY {

    private Long_KeY() {
        //Utility class
    }

    /*@ normal_behavior
      @
      @ ensures \result.length == 8;
      @ ensures value == fromBytes(\result);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
    static /*@pure@*/ byte[] toBytes(long value) {
        byte[] result = new byte[8];
        result[0] = (byte) (value >> (56)   );
        result[1] = (byte) (value >> (48)   );
        result[2] = (byte) (value >> (40)   );
        result[3] = (byte) (value >> (32)   );
        result[4] = (byte) (value >> (24)   );
        result[5] = (byte) (value >> (16)   );
        result[6] = (byte) (value >> (8)    );
        result[7] = (byte) (value           );
        return result;
    }

    /*@ normal_behavior
      @
      @ requires bytes != null; //JJBMC does not assume all parameters to be non-null by default like KeY, so we need to specify the precondition explicitly
      @ requires bytes.length == 8;
      @ ensures \result == fromBytes(bytes);
      @ assignable \strictly_nothing;
      @*/
    static /*@pure@*/ long fromBytes(byte[] bytes) {
        return    ((long) (bytes[0] & 0xFF) << (56) )
                ^ ((long) (bytes[1] & 0xFF) << (48) )
                ^ ((long) (bytes[2] & 0xFF) << (40) )
                ^ ((long) (bytes[3] & 0xFF) << (32) )
                ^ ((long) (bytes[4] & 0xFF) << (24) )
                ^ ((long) (bytes[5] & 0xFF) << (16) )
                ^ ((long) (bytes[6] & 0xFF) << (8)  )
                ^ ((long) (bytes[7] & 0xFF)         );
    }
}
