package reasoner;

import java.io.File;

import org.apache.commons.cli.*;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

import ilog.concert.IloException;
import reasoner.ilp.ILPPreprocessor;


public class Main {
  
	public static void main(String[] args) throws OWLOntologyCreationException {

		System.out.println("**************     Cicada: A Tableau-based Algebraic Reasoner for DL SHOIQ     **************");
		System.out.println("");
	 /*	
		Options options = new Options();

        Option input = new Option("i", "input", true, "input file path");
        input.setRequired(true);
        options.addOption(input);
        

        CommandLineParser parser = new DefaultParser();
        HelpFormatter formatter = new HelpFormatter();
        CommandLine cmd;
        

        try {
            cmd = parser.parse(options, args);
        } catch (ParseException e) {
            System.out.println(e.getMessage());
            formatter.printHelp("utility-name", options);

            System.exit(1);
            return;
        }
        String inputFilePath = cmd.getOptionValue("input");
        File file = new File(inputFilePath);
		new TestReasoner(file).useReasoner();
		*/
		
		new TestReasoner().useReasoner();
		
	}
}
