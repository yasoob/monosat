package monosat;

import java.io.IOException;
import java.util.ArrayList;

/**
 * Simple test driver for running MonoSAT through the JAVA api via CLI.
 * Note that this is for testing purposes only, and is not the
 * recommended way to access MonoSAT from the command line
 */
public class MonosatTest {
    public static void main(String[] args){
        if(args.length<1){
            System.out.println("Requires a filename (GNF format) to read.");
            System.exit(1);
        }
        String filename = args[args.length-1];
        ArrayList<String> solver_args = new ArrayList<>();
        for(int i = 0;i<args.length-1;i++){
            solver_args.add(args[i]);
        }
        Solver s = new Solver(String.join(" ",args),false, "",false);
        try{
            s.loadConstraints(filename);
            if(s.solve()){
                System.out.println("SAT");
                System.exit(10);
            }else{
                System.out.println("UNSAT");
                System.exit(20);
            }
        }catch(IOException e){
            e.printStackTrace();
            System.exit(1);
        }
    }
}
