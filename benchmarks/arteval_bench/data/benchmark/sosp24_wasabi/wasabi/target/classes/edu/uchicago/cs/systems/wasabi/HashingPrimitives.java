package edu.uchicago.cs.systems.wasabi;

//import java.nio.charset.StandardCharsets;
//import org.apache.commons.codec.digest.MurmurHash3;
import java.util.ArrayList;

class HashingPrimitives {
  public static int getHashValue(String str1, String str2, String str3) {
    return 0;
    /*
    byte[] bytes1 = str1.getBytes(StandardCharsets.UTF_8);
    byte[] bytes2 = str2.getBytes(StandardCharsets.UTF_8);
    byte[] bytes3 = str3.getBytes(StandardCharsets.UTF_8);
    
    byte[] bytes = new byte[bytes1.length + bytes2.length + bytes3.length];
    
    System.arraycopy(bytes1, 0, bytes, 0, bytes1.length);
    System.arraycopy(bytes2, 0, bytes, bytes1.length, bytes2.length);
    System.arraycopy(bytes3, 0, bytes, bytes1.length + bytes2.length, bytes3.length);
    
    return MurmurHash3.hash32x86(bytes, 0, bytes.length, 0);
    */
  }

  public static int getHashValue(ArrayList<String> arr) {
    return 0;
    /*
    ArrayList<byte[]> byteList = new ArrayList<>();
    int totalLength = 0;
    for (String e : arr) {
      byte[] bytes = e.getBytes(StandardCharsets.UTF_8);
      byteList.add(bytes);
      totalLength += bytes.length;
    }
    
    byte[] bytes = new byte[totalLength];
    int offset = 0;
    for (byte[] b : byteList) {
      System.arraycopy(b, 0, bytes, offset, b.length);
      offset += b.length;
    }
    
    return MurmurHash3.hash32x86(bytes, 0, bytes.length, 0);
  */
  }
}
