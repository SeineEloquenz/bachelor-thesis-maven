package edu.kit.iti.formal.vser;

public interface ByteMeasurable {

    //@ public instance model int byteSize;

    /*@ public normal_behavior
      @
      @ ensures \result == (\sum int i; 0 <= i && i < measurables.length; measurables[i].byteSize);
      @ assignable \strictly_nothing;
      @*/
    public static int /*@strictly_pure@*/ byteSize(ByteMeasurable[] measurables) {
        int result = 0;
        /*@
          @ maintaining 0 <= \index && \index < measurables.length;
          @ maintaining result == (\sum int j; 0 <= j && j < \index; measurables[\index].byteSize);
          @ decreasing measurables.length - \index;
          @ assignable result;
          @*/
        for (ByteMeasurable measurable : measurables) {
            result += measurable.byteSize();
        }
        return result;
    }

    /*@ public normal_behavior
      @ ensures \result == byteSize;
      @ assignable \strictly_nothing;
      @*/
    public int /*@strictly_pure@*/ byteSize();

}
