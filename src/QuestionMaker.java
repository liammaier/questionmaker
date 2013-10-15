import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.*;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.semanticweb.owlapi.util.*;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

// Zachary Stark-MacMillan - 9/23/11 
// These are mostly a bunch of static functions that will probably be needed for the 
// full project of generating questions from an Protege OWL Ontology

// GREAT RESOURSE: http://owlapi.sourceforge.net/documentation.html

public class QuestionMaker {

	// generates a question / answer pair based on a given axiom and adds it to the given HashMap of questions
	public static HashMap<String, String> axiomToQuestion (OWLAxiom a, HashMap<String, String> questionMap){
		
		// each type of axiom has a different format of it's IRI so first we find which type it is
		// then deconstruct it to make the question
//		System.out.println(a.getAxiomType());
		if (a.getAxiomType() ==  AxiomType.OBJECT_PROPERTY_ASSERTION) {
			// ObjectPropertyAssertion(<http://www.semanticweb.org/ontologies/2011/7/chapter10.owl#NAME1> <http://www.semanticweb.org/ontologies/2011/7/chapter10.owl#NAME2> <http://www.semanticweb.org/ontologies/2011/7/chapter10.owl#NAME3>)
			String[] round1 = a.toString().replace('_', ' ').split("#");
			
			for (int i =1; i <round1.length ; i ++) {
				round1[i] = round1[i].split(">")[0];
			}
			// NAME2 NAME1 _______. Answer: NAME3
			questionMap.put(round1[2] + " " + round1[1] + " _________", round1[3]);
			
		} else if (a.getAxiomType() ==  AxiomType.DATA_PROPERTY_ASSERTION) {
			// DataPropertyAssertion(<http://www.semanticweb.org/ontologies/2011/7/chapter10.owl#NAME1> <http://www.semanticweb.org/ontologies/2011/7/chapter10.owl#NAME2> "DATA")
			String[] round1 = a.toString().replace('_', ' ').split("#");
			String[] result = new String[3];
			
			result[0] = round1[1].split(">")[0];
			result[1] = round1[2].split(">")[0];
			result[2] = round1[2].split(">")[1].split("\"")[1].split("\"")[0];
			
			// What is the NAME1 of NAME2?  A: NAME3
			questionMap.put("What is the " + result[0] + " of " + result[1] + "? ", result[2]);
		} else if (a.getAxiomType() ==  AxiomType.CLASS_ASSERTION) {
			// ClassAssertion(<http://www.semanticweb.org/ontologies/2011/7/chapter10.owl#NAME1> <http://www.semanticweb.org/ontologies/2011/7/chapter10.owl#NAME2>)
			String[] round1 = a.toString().replace('_', ' ').split("#");
			String[] result = new String[3];
			String class1 = null;
			String class2 = null;
			String indiv1 = null;
			String indiv2 = null;
			//System.out.println(round1[0]);
			//System.out.println(round1[1]);
			//System.out.println(round1[2]);
			
			result[0] = round1[2].split(">")[0];
			result[1] = round1[1].split(">")[0];
			
			
			// NAME1 is a _____. A: NAME2
				Set s = a.getIndividualsInSignature();
				Iterator i =s.iterator();
				while(i.hasNext()){
					OWLNamedIndividual o =(OWLNamedIndividual) i.next();
					if(indiv1 == null)indiv1 = o.toString().split("#")[1].split(">")[0].replace("_", " ");
					else indiv2 = o.toString().split("#")[1].split(">")[0];
					
					//System.out.println(o.toString());
				}
				Set se = a.getClassesInSignature();
				Iterator it =se.iterator();
				while(it.hasNext()){
					OWLClass c = (OWLClass) it.next();
					if(class1 == null)class1 = c.toString().split("#")[1].split(">")[0].replace("_", " ");
					else class2 = c.toString().split("#")[1].split(">")[0];
					
					//System.out.println(c.toString());
				}
				if(indiv2 == null){
					if(indiv1.equals(result[0])){
						questionMap.put(indiv1+ " is _______", result[1] );
					}else{
						if(class1 != null){
							if(class2 != null){
								questionMap.put(indiv1+ " " +result[1]+" "+ result[0]+ ": _______", class1 +" , "+ class2 );
							}else{
							if(class1.equals(result[0])){
								questionMap.put(indiv1+ " " +result[1]+ ": _______", result[0] );
							}
							
							}
							
						}else{
							questionMap.put(indiv1+ " is " +result[1]+ ": _______", result[0] );
						}
						
					}
				}else{
					questionMap.put(indiv1 +" "+ result[1] + ": _______", indiv2 );
				}
		} else if (a.getAxiomType() ==  AxiomType.SUBCLASS_OF) {
			String[] round1 = a.toString().replace('_', ' ').split("#");
			//classes
			String class1 = round1[1].split(">")[0];
			String class2 = round1[2].split(">")[0];
			
			System.out.println(class1+ " is " +class2);
		} else if (a.getAxiomType() ==  AxiomType.EQUIVALENT_CLASSES) {

//			String type = a;
			System.out.println(a.getObjectPropertiesInSignature());

			String[] classes = a.getClassesInSignature().toString().replace('_', ' ').split("#");
			//classes
			String class1 = classes[1].split(">")[0];
			String relation =  a.getObjectPropertiesInSignature().toString().replace('_', ' ').split("#")[0].split(">")[0];
			String class2 = classes[3].split(">")[0];
			
			System.out.println("Some" + class1 + " " + relation + " " + class2);

		}
		
		return questionMap;
	}
	
	// allows to use axiomToQuestion without an existing questionMap. Good for doing one question at a time.
	public static HashMap<String, String> axiomToQuestion (OWLAxiom a) {
		return axiomToQuestion(a, new HashMap<String, String>());
	}
	
	// retrieve a single individual given a string of it's name
	public static OWLNamedIndividual findIndividual(OWLOntology ont, String name){
		// there might be a better way to do this but I couldn't find one
		for (OWLNamedIndividual i :ont.getIndividualsInSignature()){	
			if (QuestionMaker.getName(i).equals(name)) {
				return i;
			}
		}
		return null;
	}
	
	// finds the axioms that relate two individuals
	public static HashSet<OWLAxiom> findRelation (OWLOntology ontology, OWLNamedIndividual ind1, OWLNamedIndividual ind2){
		
		if (ind1 == ind2) // so it's not checking against itself
			return null;
		
		Set<OWLAxiom> axioms = ontology.getReferencingAxioms(ind1);
		
		HashSet<OWLAxiom> matching = new HashSet<OWLAxiom>();
		
		// Cycle through each axiom that ind1 has to check to see if ind2 is there
		for (OWLAxiom a : axioms){
			if (a.getIndividualsInSignature().contains(ind2)){
				matching.add(a);
			}
		}
		if (matching.size() != 0)
			return matching;
		else 
			return null;	
	}
	
    // FIND MOST FREQUENTLY REFERENCED INDIVDUALS
	@SuppressWarnings("unchecked")
	public static HashMap<OWLNamedIndividual, Integer> getFrequentIndividuals (OWLOntology ontology){
		// NOTE: You may get different results depending on if you put the inferences into the ontology first or not
        
		// get all the axioms in the ontology
        Set<OWLAxiom> axioms = ontology.getAxioms();
        
        // make list with every occurrence of individuals 
        ArrayList<OWLNamedIndividual> individualList = new ArrayList<OWLNamedIndividual>();
        for (OWLAxiom axiom : axioms){
            individualList.addAll(axiom.getIndividualsInSignature());
        }
        
        // get a list of each unique individual 
        HashSet<OWLNamedIndividual> individualSet = new HashSet<OWLNamedIndividual>(individualList);
        
        // we'll store the frequencies of each individual in a hash
        HashMap<OWLNamedIndividual, Integer> individualFreqs = new HashMap<OWLNamedIndividual, Integer>();
        // System.out.println(individualFreqs);
        // loop through each individual in the list to check frequency
        for (OWLNamedIndividual ind : individualSet){
        	individualFreqs.put(ind, Collections.frequency(individualList, ind));
        }
             
        // sort
        individualFreqs = QuestionMaker.sortHashMapByValuesD(individualFreqs);
		
        return individualFreqs;
	}
	
	// retrieved the most frequently referenced classes
	@SuppressWarnings("unchecked")
	public static HashMap<OWLClass, Integer> getFrequentClasses (OWLOntology ontology){
		// NOTE: You may get different results depending on if you put the inferences into the ontology first or not
		
        // get all the axioms in the ontology
        Set<OWLAxiom> axioms = ontology.getAxioms();
        
        // make list with every occurrence of classes
        ArrayList<OWLClass> classList = new ArrayList<OWLClass>();
        for (OWLAxiom axiom : axioms){
            classList.addAll(axiom.getClassesInSignature());
        }
        
        // get a list of each unique  class
        HashSet<OWLClass> classSet = new HashSet<OWLClass>(classList);
        
        // we'll store the frequencies of each class in a hash
        HashMap<OWLClass, Integer> classFreqs = new HashMap<OWLClass, Integer>();
        
        // loop through each class in the list to check frequency
        for (OWLClass c : classSet){
        	classFreqs.put(c, Collections.frequency(classList, c));
        }
        
        // sort
        classFreqs = QuestionMaker.sortHashMapByValuesD(classFreqs);
        
        return classFreqs;
	}
	
	// returns a set of all the axioms that are annotated as "Important"
	public static Set<OWLAxiom> getImportantAxioms(OWLOntology ontology){
		
        // get all the axioms in the ontology
        Set<OWLAxiom> axioms = ontology.getAxioms();
        
        // result set
        Set<OWLAxiom> important = new HashSet<OWLAxiom>();
        
        for (OWLAxiom a : axioms){
        	//System.out.println(a);
        	Set<OWLClass> classes = a.getClassesInSignature();
        	//important.add(a);
        	for(OWLClass current: classes){
       		//System.out.println(current);
	            for (OWLAnnotation annotation : current.getAnnotations(ontology)){ // get the annotations for each axiom
	            	
	            	OWLLiteral value = (OWLLiteral) annotation.getValue();
	            	if (value.toString().contains("Important")){
	            		
	            		important.add(a);
	            		System.out.println(important +"\n");
	            	}
	            }
        	}
        }
        return important;
	}
	// returns a set of all the axioms that are annotated as "Important"
	public static ArrayList<OWLClassAxiom> getAllClassAxioms(OWLOntology ontology){
		ArrayList<OWLClassAxiom> set = new ArrayList<OWLClassAxiom>();
		for(OWLClass c : ontology.getClassesInSignature(true)){
			 // get all the axioms in the ontology
			set.addAll(ontology.getAxioms(c));
		}
		return set;
  	}
	// returns a set of all the axioms
	public static Set<OWLAxiom> getAllAxioms(OWLOntology ontology){
		
        // get all the axioms in the ontology
        return ontology.getAxioms();
        
	}
	// generates all the inferred axioms for an ontology and adds them to the given ontology
	public static void addInferredAxioms (OWLOntologyManager man, OWLOntology ont){
		// REFERENCE: http://owlapi.svn.sourceforge.net/viewvc/owlapi/v3/trunk/examples/src/main/java/org/coode/owlapi/examples/Example11.java?view=markup
		
        // Create a reasoner factory.  
         OWLReasonerFactory reasonerFactory = new Reasoner.ReasonerFactory();
                
        // Create the reasoner and classify the ontology
        OWLReasoner reasoner = reasonerFactory.createNonBufferingReasoner(ont);
        reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);

        // To generate an inferred ontology we use implementations of inferred axiom generators
        // to generate the parts of the ontology we want (e.g. subclass axioms, equivalent classes
        // axioms, class assertion axiom etc. - see the org.semanticweb.owlapi.util package for more
        // implementations).  
        // Set up our list of inferred axiom generators
        List<InferredAxiomGenerator<? extends OWLAxiom>> gens = new ArrayList<InferredAxiomGenerator<? extends OWLAxiom>>();
        // here is all of them
        gens.add(new InferredSubClassAxiomGenerator());
        gens.add(new InferredSubObjectPropertyAxiomGenerator() );
        gens.add(new InferredClassAssertionAxiomGenerator() );
        gens.add(new InferredInverseObjectPropertiesAxiomGenerator() );
        gens.add(new InferredPropertyAssertionGenerator() );
        gens.add(new InferredDataPropertyCharacteristicAxiomGenerator() );
        gens.add(new InferredDisjointClassesAxiomGenerator() );
        gens.add(new InferredEquivalentClassAxiomGenerator() );
        gens.add(new InferredEquivalentDataPropertiesAxiomGenerator() );
        gens.add(new InferredEquivalentObjectPropertyAxiomGenerator() );
        gens.add(new InferredSubClassAxiomGenerator() );
        gens.add(new InferredObjectPropertyCharacteristicAxiomGenerator() );
        gens.add(new InferredSubDataPropertyAxiomGenerator() );
        gens.add(new InferredSubObjectPropertyAxiomGenerator() );
                
        // Create the generator and add them to our ontology
        InferredOntologyGenerator iog = new InferredOntologyGenerator(reasoner, gens);
        iog.fillOntology(man, ont);
	}
	
	
    public static void main(String[] args) {

        try {
            // Get hold of an ontology manager
            OWLOntologyManager manager = OWLManager.createOWLOntologyManager();

            // Create a file object that points to the local copy
            File file = new File("src/elephantArticle.owl");

            // Now load the local copy
            OWLOntology ontology = manager.loadOntologyFromOntologyDocument(file);
            System.out.println("Loaded ontology: " + ontology);

            // add inferred axioms
            //QuestionMaker.addInferredAxioms(manager, ontology);
            System.out.println("Loaded ontology: " + ontology);
            // Find 'important' relations
            //Set<OWLAxiom> important = QuestionMaker.getImportantAxioms(ontology);
            ArrayList<OWLClassAxiom> all = QuestionMaker.getAllClassAxioms(ontology);
            System.out.println("Loaded ontology: " + all);
            // Print out the pairs for debugging 
            for (OWLClassAxiom a : all){
            	// System.out.println(a);
            	String question =axiomToQuestion(a).toString();
            	if(!question.equals("{}"))System.out.println(question);
            }

            
            // Remove the ontology again so we can reload it later
            manager.removeOntology(ontology);

        }
        catch (OWLOntologyCreationIOException e) {
            // IOExceptions during loading get wrapped in an OWLOntologyCreationIOException
            IOException ioException = e.getCause();
            if (ioException instanceof FileNotFoundException) {
                System.out.println("Could not load ontology. File not found: " + ioException.getMessage());
            }
            else if (ioException instanceof UnknownHostException) {
                System.out.println("Could not load ontology. Unknown host: " + ioException.getMessage());
            }
            else {
                System.out.println("Could not load ontology: " + ioException.getClass().getSimpleName() + " " + ioException.getMessage());
            }
        }
        catch (UnparsableOntologyException e) {
            // If there was a problem loading an ontology because there are syntax errors in the document (file) that
            // represents the ontology then an UnparsableOntologyException is thrown
            System.out.println("Could not parse the ontology: " + e.getMessage());
            // A map of errors can be obtained from the exception
            Map<OWLParser, OWLParserException> exceptions = e.getExceptions();
            // The map describes which parsers were tried and what the errors were
            for (OWLParser parser : exceptions.keySet()) {
                System.out.println("Tried to parse the ontology with the " + parser.getClass().getSimpleName() + " parser");
                System.out.println("Failed because: " + exceptions.get(parser).getMessage());
            }
        }
        catch (UnloadableImportException e) {
            // If our ontology contains imports and one or more of the imports could not be loaded then an
            // UnloadableImportException will be thrown (depending on the missing imports handling policy)
            System.out.println("Could not load import: " + e.getImportsDeclaration());
            // The reason for this is specified and an OWLOntologyCreationException
            OWLOntologyCreationException cause = e.getOntologyCreationException();
            System.out.println("Reason: " + cause.getMessage());
        }
        catch (OWLOntologyCreationException e) {
            System.out.println("Could not load ontology: " + e.getMessage());
        }
    }
    
    // this is the start of a function to intelligently generate questions based on how often terms are used in the ontology
    public static void generateQuestionsBasedOnFrequency (OWLOntology ontology){
    	
        // we'll store the frequencies of each individual and class in a hash
        HashMap<OWLNamedIndividual, Integer> individualFreqs = getFrequentIndividuals (ontology);
        
        // FIND AXIOMS WITH 2 COMMON INDIVUDIALS
        
        HashSet<OWLAxiom> questions = new HashSet<OWLAxiom>();
        
        HashSet<OWLAxiom> result = new HashSet<OWLAxiom>();
        
        int count = 0;

        for (OWLNamedIndividual i1 : individualFreqs.keySet()){
        	for (OWLNamedIndividual i2 : individualFreqs.keySet()){
        		result = findRelation(ontology, i1,i2); 
        		if ( result != null){
        			questions.addAll(result);
        			count ++;
        			
        			if (count > 9) // just for testing
        				break; 
        		}
        	}
        	break; // just for testing
        }
        
        // next step would be to cut off individual freqs list at a reasonable amount so you're only getting the most useful ones
        
    }
	
    // Returns the name of an entity given it's whole IRI
	public static String getName (OWLEntity e){
		// <http://www.semanticweb.org/ontologies/2011/7/chapter10.owl#NAME>
		return e.getSignature().toString().split("#")[1].split(">")[0].replace('_', ' ');
	}
	
	// Sorts a hash map, descending. Used to sort things by their frequency
	@SuppressWarnings({ "rawtypes", "unchecked" })
	public static LinkedHashMap sortHashMapByValuesD(HashMap passedMap) {
	    List mapKeys = new ArrayList(passedMap.keySet());
	    List mapValues = new ArrayList(passedMap.values());
	    Collections.sort(mapValues, Collections.reverseOrder() );
	    Collections.sort(mapKeys, Collections.reverseOrder() );
	        
	    LinkedHashMap sortedMap = 
	        new LinkedHashMap();
	    
	    Iterator valueIt = mapValues.iterator();
	    while (valueIt.hasNext()) {
	        Object val = valueIt.next();
	        Iterator keyIt = mapKeys.iterator();
	        
	        while (keyIt.hasNext()) {
	            Object key = keyIt.next();
	            String comp1 = passedMap.get(key).toString();
	            String comp2 = val.toString();
	            
	            if (comp1.equals(comp2)){
	                passedMap.remove(key);
	                mapKeys.remove(key);
	                sortedMap.put(key, val);
	                break;
	            }
	        }
	    }
	    return sortedMap;
	}
}