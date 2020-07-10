import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Random;


public class Main {
    protected static int n;            // # of variables
    protected static int m;            // # of constraints
    protected static int[] C;          // coefficients of OF
    protected static int[][] A;        // coefficients of constraints
    protected static int[] B;          // RHS
    protected static int[] X;          // solution
    protected static int[] G;          // part sums of LHS
    protected static int z;            // the value of OF

    protected static long start;       // start time
    protected static long end;         // end time
    protected static long elapsedTime; // lapsed time

    protected static String fileName;  // name of processed file
    protected static String method;    // name of the heuristic used

    protected static void ReadData(String fname) throws IOException {
        try {
            File f = new File(fname);
            BufferedReader bReader = new BufferedReader(new FileReader(f));

            // first row is: n m
            String fileRow = bReader.readLine();
            String[] splitRow = fileRow.split(" ");
            n = Integer.parseInt(splitRow[0]); // number of variables
            m = Integer.parseInt(splitRow[1]); // number of constraints

            X = new int[n];

            // the second row is for the coefficients of OF
            C = new int[n];
            fileRow = bReader.readLine();
            splitRow = fileRow.split(" ");

            for (int j = 0; j < n; j++)
                C[j] = Integer.parseInt(splitRow[j]);

            // next m rows are for coefficients of constraints
            A = new int[m][n];

            G = new int[m];

            int k = 0;
            while (k < m) {
                fileRow = bReader.readLine();
                splitRow = fileRow.split(" ");
                for (int h = 0; h < n; h++)
                    A[k][h] = Integer.parseInt(splitRow[h]);
                k = k + 1;
            }

            // the last row if for RHS
            String lastrow = bReader.readLine();
            String[] lw = lastrow.split(" ");
            B = new int[m];
            for (int l = 0; l < m; l++)
                B[l] = Integer.parseInt(lw[l]);

            bReader.close();

        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    protected static void PrintResult() throws IOException {
        try {
            File rFile = new File("result.txt");
            FileWriter bWriter = new FileWriter(rFile, true);
            bWriter.write("METHOD: >> " + method + " <<");
            z = 0;   // objective function
            System.out.println("FILE: " + fileName + "\nMethod : " + method);
            System.out.println("ET = " + elapsedTime + " ms");
            bWriter.write("\nET = " + elapsedTime + " ms");
            //System.out.print("X = (");
            //bWriter.write("X = (");
            int testG[] = new int[m];
            for (int i = 0; i < m; i++)
                testG[i] = 0;

            for (int i = 0; i < n; i++) {
                //System.out.print(X[i] + ",");
                //bWriter.write(X[i] + ",");
                z += C[i] * X[i];
                for (int j = 0; j < m; j++)
                    testG[j] += A[j][i] * X[i];
            }
            //System.out.println(")");
            //bWriter.write(")\n");
            for (int i = 0; i < m; i++)
                if (testG[i] > B[i]) System.out.println("!! Violation of constraint #" + i + "!!");
            System.out.println("Z = " + z);
            bWriter.write("\nZ = " + z + "\n\n");
            bWriter.close();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    // check constraints for element j
    protected static boolean checkConstraints(int j) {
        //System.out.println("CC: j = " + j);
        int i = 0;
        while (i < m) {
            if (G[i] + A[i][j] > B[i]) return false;
            i++;
        }
        return true;
    }
    
    protected static boolean checkConstraintsGeneticAlgorithm(int[] RX) {
    	int[] RG = new int[m];
    	for (int l = 0; l < m; l++) {
            RG[l] = 0;

        }
    	
    	for (int l = 0; l < m; l++) {
            for (int s = 0; s < n; s++) {

                RG[l] += A[l][s] * RX[s];

            }
        }
        
        	for(int j = 0;j<m;j++) {
            if (RG[j] > B[j]) return false;
            
        	}
        return true;
    }

    // check constraints for replacing 1 at position a with two 1s at positions j and c
    protected static boolean checkConstraints2(int a, int j, int c) {

        int X2[] = new int[n];

        for (int l = 0; l < n; l++)
            X2[l] = X[l];

        X2[a] = 0;
        X2[j] = 1;
        X2[c] = 1;

        for (int l = 0; l < m; l++)
            if (G[l] - A[l][a] + A[l][j] + A[l][c] > B[l]) return false;

        float z1 = 0;
        float z2 = 0;
        for (int p = 0; p < n; p++) {
            z1 += C[p] * X[p];
            z2 += C[p] * X2[p];
        }
        if (z1 > z2) return false;

        return true;
    }

    protected static boolean checkConstraints3(int a, int j) {
        //System.out.println("CC: j = " + j);
        int i = 0;
        int X2[] = new int[n];
        for (int l = 0; l < n; l++) {
            X2[l] = X[l];

        }
        X2[a] = 0;
        X2[j] = 1;

        int G2[] = new int[m];
        for (int l = 0; l < m; l++) {
            G2[l] = 0;

        }
        for (int l = 0; l < m; l++) {
            for (int s = 0; s < n; s++) {

                G2[l] += A[l][s] * X2[s];

            }
        }
        while (i < m) {
            if (G2[i] > B[i]) return false;
            i++;
        }
        float z1 = 0;
        float z2 = 0;
        for (int p = 0; p < n; p++) {
            z1 += C[p] * X[p];
            z2 += C[p] * X2[p];

        }
        if (z1 > z2) return false;

        return true;
    }
    
    


    // filling two ArrayLists with indices of 1s and 0s in the solution
    protected static void IndicesLists(ArrayList<Integer> L1, ArrayList<Integer> L0) {
        for (int i = 0; i < n; i++)
            if (X[i] == 1) L1.add(i);
            else L0.add(i);
    }


    protected static void CH_ComputeRatio() {
        method = "ComputeRatio";
        for (int i = 0; i < n; i++)
            X[i] = 0;
        int x = n;

        start = System.nanoTime(); // beginning of the timer

        G = new int[m];
        for (int i = 0; i < m; i++)
            G[i] = 0;

        ArrayList<Float> tempArray = new ArrayList<Float>(n);

        for (int i = 0; i < n; i++) {
            int sum = 0;
            for (int j = 0; j < m; j++)
                sum += A[j][i];
            float sum2 = (float) C[i] / sum;
            tempArray.add(sum2);
        }

        while (x != 0) {
            // looking for index of element with the highest coef.
            int j = tempArray.indexOf(Collections.max(tempArray));

            // verifying the constraints
            if (checkConstraints(j))
                X[j] = 1; //  here, if the condition is not respected we just have to set one value to zero and not the whole column

            for (int i = 0; i < m; i++)
                G[i] = G[i] + A[i][j] * X[j];

            tempArray.set(j, (float) 0.0);
            //System.out.println(x);
            x--;
        }

        end = System.nanoTime();  // end of the timer
        elapsedTime = (end - start) / 1000000;   // duration of the algorithm
    }

    // best heuristic from 2019
    protected static void CH_KeekedComputeRatio() {
        method = new Throwable().getStackTrace()[0].getMethodName();
        for (int i = 0; i < n; i++)
            X[i] = 0;

        int x = n;

        int R[] = new int[m]; // residual resources
        ArrayList<Integer> procElem = new ArrayList<Integer>(); // to store indices of already processed elements (i.e., where x = 1)

        for (int i = 0; i < m; i++)
            G[i] = 0;

        ArrayList<Double> tempArray = new ArrayList<Double>(n);

        start = System.nanoTime(); // beginning of the timer
        while (x > 0) {
            for (int i = 0; i < m; i++)
                R[i] = B[i] - G[i];
            // looking for index of element with the highest coef.
            for (int i = 0; i < n; i++) {
                double sum2;

                if (!(procElem.contains(i))) {
                    double sum = 0;
                    double divRes = 0;

                    double sqrRes = 0;
                    for (int j = 0; j < m; j++) {
                        if (R[j] != 0) {

                            divRes = A[j][i] / (double) R[j];
                            sqrRes = Math.pow(divRes, 2.0);

                            sum += sqrRes;
                        } else {
                            x = 0;
                            break;
                        }
                    }
                    sum2 = (double) C[i] / Math.sqrt(sum);
                } else sum2 = 0.0;
                tempArray.add(sum2);

            }

            int j = tempArray.indexOf(Collections.max(tempArray));

            // if j is not feasible, then look for another j until there are free indices
            while ((Collections.max(tempArray) > 0.0) && !(checkConstraints(j))) {
                tempArray.set(j, 0.0);
                j = tempArray.indexOf(Collections.max(tempArray));
            }

            // verifying the constraints
            if (checkConstraints(j)) {
                X[j] = 1;
                procElem.add(j); // here, if the condition is not respected we just have to set one value to zero and not the whole column
                //System.out.println("PROC: " + procElem.get(0));

                for (int i = 0; i < m; i++)
                    G[i] = G[i] + A[i][j] * X[j];
            }

            x--;
            tempArray.clear();
        }

        end = System.nanoTime();  // end of the timer
        elapsedTime = (end - start) / 1000000;   // duration of the algorithm
    }

    // Look for each pair of 0s to replace one 1
    protected static void IH_ExhaustiveSearch() {
        method = new Throwable().getStackTrace()[0].getMethodName();

        start = System.nanoTime(); // beginning of the timer

        ArrayList<Float> tempArray2 = new ArrayList<Float>(n);
        ArrayList<Float> tempArray3 = new ArrayList<Float>(n);
        for (int i = 0; i < n; i++) {
            int sum = 0;

            for (int j = 0; j < m; j++)
                sum += A[j][i];

            float sum2 = (float) C[i] / sum;

            tempArray3.add(sum2);
            tempArray2.add(sum2);
        }

        //Collections.sort(tempArray3, Collections.reverseOrder());
        Collections.sort(tempArray3);

        int bestS = 0;
        int bestY = 0;

        ArrayList<Integer> OneIndexTable = new ArrayList<Integer>();
        ArrayList<Integer> ZeroIndexTable = new ArrayList<Integer>();

        IndicesLists(OneIndexTable, ZeroIndexTable);

        for (int i = 0; i < n; i++) {
            bestS = -1;
            bestY = -1;
            //System.out.println(tempArray3.get(i));
            int b = tempArray2.indexOf(tempArray3.get(i));
            //System.out.println(b);
            if (X[b] == 1) {
                for (int s = 0; s < ZeroIndexTable.size() - 1; s++) {
                    for (int y = s + 1; y < ZeroIndexTable.size() - 1; y++) {
                        int valueOfS = ZeroIndexTable.get(s);
                        int valueOfY = ZeroIndexTable.get(y);
                        if (C[b] < C[valueOfS] + C[valueOfY]) {
                            X[b] = 0;
                            X[valueOfS] = X[valueOfY] = 1;
                            if (checkConstraints2(b, valueOfS, valueOfY)) {

                                bestS = valueOfS;
                                bestY = valueOfY;
                            }
                            X[b] = 1;
                            X[valueOfS] = X[valueOfY] = 0;
                        }
                    }
                }
                if (bestS != -1) {
                    X[bestS] = X[bestY] = 1;
                    X[b] = 0;
                    ZeroIndexTable.add(b);
                    ZeroIndexTable.remove(ZeroIndexTable.indexOf(bestS));
                    ZeroIndexTable.remove(ZeroIndexTable.indexOf(bestY));
                    for (int t = 0; t < m; t++)
                        G[t] = G[t] - A[t][b] + A[t][bestS] + A[t][bestY];
                }
            }
        }

        end = System.nanoTime();  // end of the timer
        elapsedTime = (end - start) / 1000000;   // duration of the algorithm
    }


    protected static void IH_RandomizedComputeRatio() {
        method = "RandomizedComputeRatio";
        start = System.nanoTime(); // beginning of the timer
        ArrayList<Integer> OneIndexTable = new ArrayList<Integer>();
        ArrayList<Integer> ZeroIndexTable = new ArrayList<Integer>();

        for (int i = 0; i < n; i++) {
            if (X[i] == 1) OneIndexTable.add(i);
            else ZeroIndexTable.add(i);
        }

        int r1 = 0;
        int r2 = 0;
        int u = 0;
        Random rand = new Random();
        while (u < 1000) {
            r1 = rand.nextInt(OneIndexTable.size());
            r2 = rand.nextInt(ZeroIndexTable.size());

            if (checkConstraints3(OneIndexTable.get(r1), ZeroIndexTable.get(r2))) {
                X[OneIndexTable.get(r1)] = 0;
                X[ZeroIndexTable.get(r2)] = 1;
                int temp = OneIndexTable.get(r1);
                OneIndexTable.set(r1, ZeroIndexTable.get(r2));
                ZeroIndexTable.set(r2, temp);
            }
            u++;
        }
        end = System.nanoTime();  // end of the timer
        elapsedTime = (end - start) / 1000000;   // duration of the algorithm
    }


    protected static void IH_MixedComputeRatio() {
        method = "MixedComputeRatio";

        start = System.nanoTime(); // beginning of the timer
        ArrayList<Float> tempArray = new ArrayList<Float>(n);
        ArrayList<Float> tempArray2 = new ArrayList<Float>(n);
        ArrayList<Float> tempArray3 = new ArrayList<Float>(n);

        for (int i = 0; i < n; i++) {
            int sum = 0;
            for (int j = 0; j < m; j++) {
                sum += A[j][i];
            }
            float sum2 = (float) C[i] / sum;
            tempArray.add(sum2);
            tempArray2.add(sum2);
            tempArray3.add(sum2);
            //System.out.println("TempArray[i] : "+tempArray.get(i));
        }
        Collections.sort(tempArray3, Collections.reverseOrder());


        start = System.nanoTime(); // beginning of the timer


        end = System.nanoTime();  // end of the timer
        elapsedTime = (end - start) / 1000000;   // duration of the algorithm


        // Improved heuristic

        ArrayList<Integer> OneIndexTable = new ArrayList<Integer>();   // tables with the indices of the the 1 in X
        ArrayList<Integer> ZeroIndexTable = new ArrayList<Integer>();    // tables with the indices of the the 0 in X

        for (int i = 0; i < n; i++) {

            if (X[i] == 1) {

                OneIndexTable.add(i);
            } else {
                ZeroIndexTable.add(i);

            }
        }
        Random rand = new Random();
        int r2 = rand.nextInt(ZeroIndexTable.size());


        for (int i = 0; i < n; i++) {
            int b = tempArray2.indexOf(tempArray3.get(i));  // pick the ith element of temparray3 so the ith element with the most important coefficient
            if (X[b] == 1) {
                for (int j = 1; j < n; j++) {
                    int c = tempArray2.indexOf(tempArray3.get(j));
                    if (X[c] == 0) {
                        int d = ZeroIndexTable.get(r2);

                        if (checkConstraints2(b, c, d)) {
                            X[b] = 0;
                            X[c] = X[d] = 1;
                            //tempArray3.remove(i);
                            for (int w = 0; w < m; w++) {
                                G[w] = G[w] + A[w][c] * X[c] + A[w][d] * X[d] - A[w][b] * X[b];

                            }
                        }
                    }
                }
            }
        }
        end = System.nanoTime();  // end of the timer
        elapsedTime = (end - start) / 1000000;   // duration of the algorithm
    }
    
    
    // Heuristic 1. Just max coef of OF
    protected static void BruteForce() {
        method = "Bruteforce";
        // clear the solution
        for (int i = 0; i < n; i++) {
            X[i] = 0;
        }
        // clear LHS
        G = new int[m];
        for (int i = 0; i < m; i++)
            G[i] = 0;

        ArrayList<Integer> tmpList = new ArrayList<Integer>(n);   // temporary array of coef. of OF
        int v = 0;
        while (v < n) {
            tmpList.add(C[v]);
            v = v + 1;
        }

        start = System.nanoTime(); // beginning of the timer

        while (tmpList.size() != 0) {
            // looking for index of element with the highest coef.
            int j = tmpList.indexOf(Collections.max(tmpList));
            // verifying the constraints
            if (checkConstraints(j)) {
                X[j] = 1;
                for (int i = 0; i < m; i++)
                    G[i] = G[i] + A[i][j];
            }

            // removing chosen variable
            tmpList.remove(j);
        }

        end = System.nanoTime();  // end of the timer
        elapsedTime = (end - start) / 1000000;   // duration of the algorithm in ms
    }
    
    protected static void Mutation(int[] RX) {
    	

    	
    	int nbOfMutations = 0;
        int r = 0;
        Random rand = new Random();
    
        nbOfMutations = 1 + (int)(Math.random()*5);
        //System.out.println(nbOfMutations);
        for(int nb=0 ; nb<nbOfMutations;nb++) {
        	
        	r = rand.nextInt(RX.length);
        	if(RX[r]==0) 
        	{
           		RX[r]=1;
        	}
        	if(RX[r]==1) 
        	{
              	RX[r]=0;
        	}
        }
    	
    }
    
    
    protected static void RandomSolution() {
   	
    	method = new Throwable().getStackTrace()[0].getMethodName();
        for (int i = 0; i < n; i++)
            X[i] = 0;

        int x = n;

        for (int i = 0; i < m; i++)
            G[i] = 0;
	
        int r = 0;
        Random rand = new Random();
                   
        for(int i=0 ; i<n;i++) {
        	
        	r = rand.nextInt(n);
        	//System.out.println(r);
        	if(X[r]==0 && checkConstraints(r)) 
        	{
           		X[r]=1;
           		
           		for (int y = 0; y < m; y++)
                    G[y] = G[y] + A[y][r];
            }
        	}
        	
        }
        
        
    
    
    protected static int ObjectiveFunction(int[] X) {
    	
    	int z = 0;
    	for (int i = 0; i < n; i++) {

             z += C[i] * X[i];
          
         }
    	
    	return z;
    }
    
    protected static void GeneticAlgorithm() {
    	
    	
    	start = System.nanoTime();
    	ArrayList<int[]> population = new ArrayList<int[]>();
    	ArrayList<Integer> OFCpopulation = new ArrayList<Integer>(); 
  
    	// Generate starting population
    	BruteForce();
    	int[] bruteForce = new int[n];
    	for(int i = 0;i<n;i++)
    		bruteForce[i]=X[i];
    	population.add(bruteForce);
    	OFCpopulation.add(ObjectiveFunction(bruteForce));
    	
    	
    	CH_KeekedComputeRatio();
    	int[] keekedComputeRatio = new int[n];
    	for(int i = 0;i<n;i++)
    		keekedComputeRatio[i]=X[i];
    	OFCpopulation.add(ObjectiveFunction(keekedComputeRatio));
    	population.add(keekedComputeRatio);
    	
    	
    	double chances = 0.0;
    	//System.out.println("OFC de bruteforce : "+ObjectiveFunction(population.get(0)));
    	for(int i = 0; i<50; i++) {
    		RandomSolution();
    		int[] randSol = new int[n];
    		chances = Math.random();
    		//System.out.println("chances : "+chances);
    		if(chances>0.9) 
    		{
    		IH_ExhaustiveSearch(); // try to add a local search in the generation of the starting population instead of just random solution
    		// but gives worse solution, not enough diversity
    		}
    		for(int j = 0;j<n;j++)
    			randSol[j]=X[j];
    		population.add(randSol);
    		OFCpopulation.add(ObjectiveFunction(randSol));
    		
    	}
    	int worstOFC = Collections.min(OFCpopulation);
    	int bestOFC = Collections.max(OFCpopulation);
    	System.out.println("starting worst ofc : "+ worstOFC);
    	
    	
    	//System.out.println("OFC of the sixth element : "+ObjectiveFunction(population.get(6)));
    	//System.out.println("OFC of the fourth element : "+ObjectiveFunction(population.get(4)));
    	/*System.out.println("verification if we've the same solutions in our population");
    	System.out.println(population.get(4));
    	System.out.println(population.get(0));*/
    	method = new Throwable().getStackTrace()[0].getMethodName();
    	for(int p=0; p<50;p++)  // having a huge p is useless because the method converges quite quickly
    	{
    	// Chose the parents and genetic operators

    	ArrayList<int[]> children = new ArrayList<int[]>();

    	for(int i = 0; i<population.size()-1;i++)
    		for(int j = i+1; j<population.size();j++) {
    			
    			int[] child = new int[n];
    			int[] child2 = new int[n];
    			int[] parent1 = population.get(i);
    			int[] parent2 = population.get(j);
    			
    			// Generating two children with the crossover operator
    			for(int k = 0; k<n/2;k++) {
    				
    					child[k]=parent1[k];
    					child2[k]=parent2[k];
    			}
    			for(int k = n/2; k<n;k++) {
    				
					child[k]=parent2[k];
					child2[k]=parent1[k];
			}
    			// Mutation for each child
    			//System.out.println("OFC child2 "+ObjectiveFunction(child2));
    			Mutation(child);
    			Mutation(child2);
    			children.add(child2);
    			children.add(child);

    		}
    			// Evaluation step
    	
    			for(int i=0; i<children.size()-1;i++) {
    			int[] child = children.get(i);

    			// Evaluation step
    			int z = ObjectiveFunction(child);
       			if(checkConstraintsGeneticAlgorithm(child) && !(OFCpopulation.contains(z))) {
       				//System.out.println("feasible solution found");
       				// we check if z is not already in our population to avoid repeating the same information
       				
       				//System.out.println(z);
       				if(population.size()<1000) 
       				{
       					population.add(child);
       					OFCpopulation.add(z);
       					worstOFC = Collections.min(OFCpopulation);
       					
       				}
       				if(population.size()>=1000 && z>worstOFC) 
       				{
       				//System.out.println("overcrowed");
       				population.add(child);
       				OFCpopulation.add(z);
       				population.remove(OFCpopulation.indexOf(worstOFC));
       				OFCpopulation.remove(OFCpopulation.indexOf(worstOFC));
       				worstOFC = Collections.min(OFCpopulation);
       				
       				if(bestOFC<z) {
       					System.out.println("BETTER SOLUTION FOUND");
       					bestOFC=z;

       				}
    			}
    			
       			}
       			
    			}
    			
    	System.out.println("Worst solution in the set : "+worstOFC);	
    	int[] bestX = population.get(OFCpopulation.indexOf(bestOFC));
    	for(int v = 0;v<n;v++)
    		X[v]=bestX[v];
    	System.out.println("p : "+p);
    	System.out.println(population.size()); // to check if our population is too big or not
    	}
    	
    	end = System.nanoTime();  // end of the timer
        elapsedTime = (end - start) / 1000000; 
        	
     // duration of the algorithm in ms
    	
    	
    	
    	
    	
    	
    }
    
protected static void GeneticAlgorithmV2() {
    	
    	
    	start = System.nanoTime();
    	ArrayList<int[]> population = new ArrayList<int[]>();
    	ArrayList<Integer> OFCpopulation = new ArrayList<Integer>(); 
  
    	// Generate starting population
    	BruteForce();
    	int[] bruteForce = new int[n];
    	for(int i = 0;i<n;i++)
    		bruteForce[i]=X[i];
    	population.add(bruteForce);
    	OFCpopulation.add(ObjectiveFunction(bruteForce));
    	
    	
    	CH_KeekedComputeRatio();
    	int[] keekedComputeRatio = new int[n];
    	for(int i = 0;i<n;i++)
    		keekedComputeRatio[i]=X[i];
    	OFCpopulation.add(ObjectiveFunction(keekedComputeRatio));
    	population.add(keekedComputeRatio);
    	
    	
    	double chances = 0.0;
    	//System.out.println("OFC de bruteforce : "+ObjectiveFunction(population.get(0)));
    	for(int i = 0; i<50; i++) {
    		RandomSolution();
    		int[] randSol = new int[n];
    		chances = Math.random();
    		//System.out.println("chances : "+chances);
    		if(chances>0.9) 
    		{
    		IH_ExhaustiveSearch(); // try to add a local search in the generation of the starting population instead of just random solution
    		// but gives worse solution, not enough diversity
    		}
    		for(int j = 0;j<n;j++)
    			randSol[j]=X[j];
    		population.add(randSol);
    		OFCpopulation.add(ObjectiveFunction(randSol));
    		
    	}
    	int worstOFC = Collections.min(OFCpopulation);
    	int bestOFC = Collections.max(OFCpopulation);
    	//System.out.println("starting worst ofc : "+ worstOFC);
    	
    	
    	//System.out.println("OFC of the sixth element : "+ObjectiveFunction(population.get(6)));
    	//System.out.println("OFC of the fourth element : "+ObjectiveFunction(population.get(4)));
    	/*System.out.println("verification if we've the same solutions in our population");
    	System.out.println(population.get(4));
    	System.out.println(population.get(0));*/
    	method = new Throwable().getStackTrace()[0].getMethodName();
    	for(int p=0; p<50;p++)  // having a huge p is useless because the method converges quite quickly
    	{
    	// Chose the parents and genetic operators

    	ArrayList<int[]> children = new ArrayList<int[]>();

    	for(int i = 0; i<population.size()-1;i++)
    		for(int j = i+1; j<population.size();j++) {
    			
    			int[] child = new int[n];
    			int[] child2 = new int[n];
    			int[] parent1 = population.get(i);
    			int[] parent2 = population.get(j);
    			int rDivide = 0;
    			Random randDivide = new Random();
    			rDivide = randDivide.nextInt(n-1)+1;
    			// Generating two children with the crossover operator
    			for(int k = 0; k<(int)n/rDivide;k++) {
    				
    					child[k]=parent1[k];
    					child2[k]=parent2[k];
    			}
    			for(int k = (int)n/rDivide; k<n;k++) {
    				
					child[k]=parent2[k];
					child2[k]=parent1[k];
			}
    			// Mutation for each child
    			//System.out.println("OFC child2 "+ObjectiveFunction(child2));
    			Mutation(child);
    			Mutation(child2);
    			children.add(child2);
    			children.add(child);

    		}
    			// Evaluation step
    	
    			for(int i=0; i<children.size()-1;i++) {
    			int[] child = children.get(i);

    			// Evaluation step
    			int z = ObjectiveFunction(child);
       			if(checkConstraintsGeneticAlgorithm(child) && !(OFCpopulation.contains(z))) {
       				//System.out.println("feasible solution found");
       				// we check if z is not already in our population to avoid repeating the same information
       				
       				//System.out.println(z);
       				if(population.size()<250) 
       				{
       					population.add(child);
       					OFCpopulation.add(z);
       					worstOFC = Collections.min(OFCpopulation);
       					
       				}
       				if(population.size()>=250 && z>worstOFC) 
       				{
       				//System.out.println("overcrowed");
       				population.add(child);
       				OFCpopulation.add(z);
       				population.remove(OFCpopulation.indexOf(worstOFC));
       				OFCpopulation.remove(OFCpopulation.indexOf(worstOFC));
       				worstOFC = Collections.min(OFCpopulation);
       				
       				if(bestOFC<z) {
       					System.out.println("BETTER SOLUTION FOUND");
       					bestOFC=z;

       				}
    			}
    			
       			}
       			
    			}
    			
    	//System.out.println("Worst solution in the set : "+worstOFC);	
    	int[] bestX = population.get(OFCpopulation.indexOf(bestOFC));
    	for(int v = 0;v<n;v++)
    		X[v]=bestX[v];
    	//System.out.println("p : "+p);
    	//System.out.println(population.size()); // to check if our population is too big or not
    	}
    	
    	end = System.nanoTime();  // end of the timer
        elapsedTime = (end - start) / 1000000; 
        	
     // duration of the algorithm in ms
    	
    	
    	
    	
    	
    	
    }
    
protected static void GeneticAlgorithmV5() {
	
	
	start = System.nanoTime();
	ArrayList<int[]> population = new ArrayList<int[]>();
	ArrayList<Integer> OFCpopulation = new ArrayList<Integer>(); 

	// Generate starting population
	int bestOFC= 0;
	
	
	BruteForce();
	int[] bruteForce = new int[n];
	for(int i = 0;i<n;i++)
		bruteForce[i]=X[i];
	population.add(bruteForce);
	OFCpopulation.add(ObjectiveFunction(bruteForce));
	
	
	CH_KeekedComputeRatio();
	int[] keekedComputeRatio = new int[n];
	for(int i = 0;i<n;i++)
		keekedComputeRatio[i]=X[i];
	OFCpopulation.add(ObjectiveFunction(keekedComputeRatio));
	population.add(keekedComputeRatio);
	bestOFC = ObjectiveFunction(keekedComputeRatio);
	
	
	System.out.println("OFC de bruteforce : "+ObjectiveFunction(population.get(0)));
	for(int i = 0; i<30; i++) {
		RandomSolution();
		int[] randSol = new int[n];
		for(int j = 0;j<n;j++)
			randSol[j]=X[j];
		population.add(randSol);
		OFCpopulation.add(ObjectiveFunction(randSol));
		
	}
	System.out.println("OFC de bruteforce : "+ObjectiveFunction(population.get(6)));
	System.out.println("OFC de bruteforce : "+ObjectiveFunction(population.get(11)));
	
	
	
	int[] parent1 = new int[n];
	int[] parent2 = new int[n];
	for(int p=0; p<10000;p++) 
	{
		
	for(int i = 0;i<n;i++)
		{
		X[i]=0;
		}
	// Chose the parents and genetic operators
	int indexP1 = 0;
	int indexP2 = 0;
	Random rand1 = new Random();
	Random rand2 = new Random();
	indexP1 = rand1.nextInt(population.size());
    indexP2 = rand2.nextInt(population.size());
	ArrayList<int[]> children = new ArrayList<int[]>();

			
			//int[] child = new int[n];
			//int[] child2 = new int[n];
			parent1 = population.get(indexP1);
			parent2 = population.get(indexP2);
			//System.out.println("Parent1 OFC : "+ObjectiveFunction(parent1));
			// Generating two children with the crossover operator
			for(int k = 0; k<n;k++) {
					
					if(k%2==0)
					{
					X[k]=parent1[k];
					}
					if(k%2==1)
					{
					X[k]=parent2[k];
					}
				
		}
			int testG[] = new int[m];
            for (int i = 0; i < m; i++)
                testG[i] = 0;
			for (int i = 0; i < n; i++) {

                for (int j = 0; j < m; j++)
                    testG[j] += A[j][i] * X[i];
            }

            for (int i = 0; i < m; i++)
                if (testG[i] > B[i]) System.out.println("!! Violation of constraint #" + i + "!!");
			// Mutation for each child
			//System.out.println("OFC child2 "+ObjectiveFunction(X));
			IH_ExhaustiveSearch();
			int[] impSol = new int[n];
			for(int j = 0;j<n;j++)
				impSol[j]=X[j];
			children.add(impSol);
			//children.add(child);
			//System.out.println("OFC child 2 after mutation : "+ObjectiveFunction(X));
		
			// Evaluation step
	
			for(int i=0; i<children.size()-1;i++) {
			int[] chosenChild = children.get(i);

   			if(checkConstraintsGeneticAlgorithm(chosenChild)) {
   				int z = ObjectiveFunction(chosenChild);
   				System.out.println("feasible new solution found");
   				population.add(chosenChild);
   				OFCpopulation.add(z);
   				if(bestOFC<z) {
   					System.out.println("better solution found");
   					bestOFC=z;

   				}
			}
			
		
			}
			
	method = new Throwable().getStackTrace()[0].getMethodName();
	int[] bestX = population.get(OFCpopulation.indexOf(bestOFC));
	for(int i = 0;i<n;i++)
		X[i]=bestX[i];
	//System.out.println("Best solution found : "+bestOFC);
	
	}
	System.out.println(population.size());
	end = System.nanoTime();  // end of the timer
    elapsedTime = (end - start) / 1000000;   // duration of the algorithm in ms
	
	
	
	
	
	
}
    
protected static void MemeticAlgorithmV2() {
	
	
	start = System.nanoTime();
	ArrayList<int[]> population = new ArrayList<int[]>();
	ArrayList<Integer> OFCpopulation = new ArrayList<Integer>(); 

	// Generate starting population
	BruteForce();
	int[] bruteForce = new int[n];
	for(int i = 0;i<n;i++)
		bruteForce[i]=X[i];
	population.add(bruteForce);
	OFCpopulation.add(ObjectiveFunction(bruteForce));
	
	
	CH_KeekedComputeRatio();
	int[] keekedComputeRatio = new int[n];
	for(int i = 0;i<n;i++)
		keekedComputeRatio[i]=X[i];
	OFCpopulation.add(ObjectiveFunction(keekedComputeRatio));
	population.add(keekedComputeRatio);
	
	
	double chances = 0.0;
    
    
	System.out.println("OFC de bruteforce : "+ObjectiveFunction(population.get(0)));
	for(int i = 0; i<75; i++) {
		RandomSolution();
		chances = Math.random();
		System.out.println("chances : "+chances);
		if(chances>0.9) 
		{
		IH_ExhaustiveSearch(); // try to add a local search in the generation of the starting population instead of just random solution
		// but gives worse solution, not enough diversity
		}
		int[] randSol = new int[n];
		for(int j = 0;j<n;j++)
			randSol[j]=X[j];
		population.add(randSol);
		OFCpopulation.add(ObjectiveFunction(randSol));
		
	}
	int worstOFC = Collections.min(OFCpopulation);
	int bestOFC = Collections.max(OFCpopulation);
	System.out.println("worst ofc : "+ worstOFC);
	
	
	System.out.println("OFC of the sixth element : "+ObjectiveFunction(population.get(6)));
	System.out.println("OFC of the fourth element : "+ObjectiveFunction(population.get(4)));
	
	method = new Throwable().getStackTrace()[0].getMethodName();
	for(int p=0; p<10000;p++) 
	{
		
	    	int[] child = new int[n];
	    	int[] child2 = new int[n];
	    	int[] parent1 = new int[n];
	    	int[] parent2 = new int[n];
	    	// Chose the parents and genetic operators
	    	int indexP1 = 0;
	    	int indexP2 = 0;
	    	int indexP3 = 0;
	    	int indexP4 = 0;
	        Random rand = new Random();
	        indexP1 = rand.nextInt(population.size());
	        indexP2 = rand.nextInt(population.size());
	        indexP3 = rand.nextInt(population.size());
	        indexP4 = rand.nextInt(population.size());
	        //System.out.println("IndexP1 :"+indexP1);
	        //System.out.println("IndexP2 :"+indexP2);
	    	ArrayList<int[]> children = new ArrayList<int[]>();
			   			
			parent1 = population.get(indexP1);
			parent2 = population.get(indexP2);
			int[] parent3 = population.get(indexP3);
			int[] parent4 = population.get(indexP4);
			
			// Generating two children with the crossover operator
			for(int k = 0; k<n/2;k++) {
					if(ObjectiveFunction(parent1)>ObjectiveFunction(parent2)) 
					{
					X[k]=parent1[k];
					}
					else 
					{
						X[k]=parent2[k];
					}
					//child2[k]=parent2[k];
					//System.out.println("child2 k coefficients coming from parent 2 : "+child2[k]);
			}
			for(int k = n/2; k<n;k++) {
				
				if(ObjectiveFunction(parent3)>ObjectiveFunction(parent4)) 
				{
				X[k]=parent3[k];
				}
				else 
				{
					X[k]=parent4[k];
				}
				//child2[k]=parent1[k];
				//System.out.println("child2 k coefficients coming from parent 2 : "+child2[k]);
		}

			// Local search for the child
			IH_ExhaustiveSearch();
			for(int i = 0;i<n;i++)
				child[i]=X[i];
										
			// Evaluation step
			int z = ObjectiveFunction(child);
   			if(checkConstraintsGeneticAlgorithm(child) && !(OFCpopulation.contains(z))) {
   				//System.out.println("feasible solution found");
   				// we check if z is not already in our population to avoid repeating the same information
   				
   				//System.out.println(z);
   				if(population.size()<300) 
   				{
   					population.add(child);
   					OFCpopulation.add(z);
   					worstOFC = Collections.min(OFCpopulation);
   					
   				}
   				if(population.size()>=300 && z>worstOFC) 
   				{
   				System.out.println("overcrowed");
   				population.add(child);
   				OFCpopulation.add(z);
   				population.remove(OFCpopulation.indexOf(worstOFC));
   				OFCpopulation.remove(OFCpopulation.indexOf(worstOFC));
   				worstOFC = Collections.min(OFCpopulation);
   				
   				if(bestOFC<z) {
   					System.out.println("BETTER SOLUTION FOUND");
   					bestOFC=z;

   				}
			}
			System.out.println(worstOFC);
   			}
			
			
	    	int[] bestX = population.get(OFCpopulation.indexOf(bestOFC));
	    	for(int m = 0;m<n;m++)
	    		X[m]=bestX[m];
	    	System.out.println("p : "+p);
	    	System.out.println("population : "+population.size()); // to check if our population is to big or not
	

	
	}
	
	end = System.nanoTime();  // end of the timer
    elapsedTime = (end - start) / 1000000;   // duration of the algorithm in ms
	 	

}



protected static void MemeticAlgorithmV4() {
	
	
	start = System.nanoTime();
	ArrayList<int[]> population = new ArrayList<int[]>();
	ArrayList<Integer> OFCpopulation = new ArrayList<Integer>(); 

	// Generate starting population
	BruteForce();
	int[] bruteForce = new int[n];
	for(int i = 0;i<n;i++)
		bruteForce[i]=X[i];
	population.add(bruteForce);
	OFCpopulation.add(ObjectiveFunction(bruteForce));
	
	
	CH_KeekedComputeRatio();
	int[] keekedComputeRatio = new int[n];
	for(int i = 0;i<n;i++)
		keekedComputeRatio[i]=X[i];
	OFCpopulation.add(ObjectiveFunction(keekedComputeRatio));
	population.add(keekedComputeRatio);
	
	
	double chances = 0.0;
    
    
	System.out.println("OFC de bruteforce : "+ObjectiveFunction(population.get(0)));
	for(int i = 0; i<75; i++) {
		RandomSolution();
		chances = Math.random();
		System.out.println("chances : "+chances);
		if(chances>0.9) 
		{
		IH_ExhaustiveSearch(); // try to add a local search in the generation of the starting population instead of just random solution
		// but gives worse solution, not enough diversity
		}
		int[] randSol = new int[n];
		for(int j = 0;j<n;j++)
			randSol[j]=X[j];
		population.add(randSol);
		OFCpopulation.add(ObjectiveFunction(randSol));
		
	}
	int worstOFC = Collections.min(OFCpopulation);
	int bestOFC = Collections.max(OFCpopulation);
	System.out.println("worst ofc : "+ worstOFC);
	
	
	System.out.println("OFC of the sixth element : "+ObjectiveFunction(population.get(6)));
	System.out.println("OFC of the fourth element : "+ObjectiveFunction(population.get(4)));
	
	method = new Throwable().getStackTrace()[0].getMethodName();
	for(int p=0; p<10000;p++) 
	{
		
	    	int[] child = new int[n];
	    	int[] child2 = new int[n];
	    	int[] parent1 = new int[n];
	    	int[] parent2 = new int[n];
	    	// Chose the parents and genetic operators
	    	int indexP1 = 0;
	    	int indexP2 = 0;
	    	int indexP3 = 0;
	    	int indexP4 = 0;
	        Random rand = new Random();
	        indexP1 = rand.nextInt(population.size());
	        indexP2 = rand.nextInt(population.size());
	        indexP3 = rand.nextInt(population.size());
	        indexP4 = rand.nextInt(population.size());
	        
	        int rDivide = 0;
			Random randDivide = new Random();
			rDivide = randDivide.nextInt(n-1)+1;
	        //System.out.println("IndexP1 :"+indexP1);
	        //System.out.println("IndexP2 :"+indexP2);
	    	ArrayList<int[]> children = new ArrayList<int[]>();
			   			
			parent1 = population.get(indexP1);
			parent2 = population.get(indexP2);
			int[] parent3 = population.get(indexP3);
			int[] parent4 = population.get(indexP4);
			
			// Generating two children with the crossover operator
			for(int k = 0; k<n/(int)rDivide;k++) {
					if(ObjectiveFunction(parent1)>ObjectiveFunction(parent2)) 
					{
					X[k]=parent1[k];
					}
					else 
					{
						X[k]=parent2[k];
					}
					//child2[k]=parent2[k];
					//System.out.println("child2 k coefficients coming from parent 2 : "+child2[k]);
			}
			for(int k = n/(int)rDivide; k<n;k++) {
				
				if(ObjectiveFunction(parent3)>ObjectiveFunction(parent4)) 
				{
				X[k]=parent3[k];
				}
				else 
				{
					X[k]=parent4[k];
				}
				//child2[k]=parent1[k];
				//System.out.println("child2 k coefficients coming from parent 2 : "+child2[k]);
		}

			// Local search for the child
			IH_ExhaustiveSearch();
			for(int i = 0;i<n;i++)
				child[i]=X[i];
										
			// Evaluation step
			int z = ObjectiveFunction(child);
   			if(checkConstraintsGeneticAlgorithm(child) && !(OFCpopulation.contains(z))) {
   				//System.out.println("feasible solution found");
   				// we check if z is not already in our population to avoid repeating the same information
   				
   				//System.out.println(z);
   				if(population.size()<300) 
   				{
   					population.add(child);
   					OFCpopulation.add(z);
   					worstOFC = Collections.min(OFCpopulation);
   					
   				}
   				if(population.size()>=300 && z>worstOFC) 
   				{
   				System.out.println("overcrowed");
   				population.add(child);
   				OFCpopulation.add(z);
   				population.remove(OFCpopulation.indexOf(worstOFC));
   				OFCpopulation.remove(OFCpopulation.indexOf(worstOFC));
   				worstOFC = Collections.min(OFCpopulation);
   				
   				if(bestOFC<z) {
   					System.out.println("BETTER SOLUTION FOUND");
   					bestOFC=z;

   				}
			}
			System.out.println(worstOFC);
   			}
			
			
	    	int[] bestX = population.get(OFCpopulation.indexOf(bestOFC));
	    	for(int m = 0;m<n;m++)
	    		X[m]=bestX[m];
	    	System.out.println("p : "+p);
	    	System.out.println("population : "+population.size()); // to check if our population is to big or not
	

	
	}
	
	end = System.nanoTime();  // end of the timer
    elapsedTime = (end - start) / 1000000;   // duration of the algorithm in ms
	 	

}



protected static void MemeticAlgorithmV3() {
	
	
	start = System.nanoTime();
	ArrayList<int[]> population = new ArrayList<int[]>();
	ArrayList<Integer> OFCpopulation = new ArrayList<Integer>(); 

	// Generate starting population
	BruteForce();
	int[] bruteForce = new int[n];
	for(int i = 0;i<n;i++)
		bruteForce[i]=X[i];
	population.add(bruteForce);
	OFCpopulation.add(ObjectiveFunction(bruteForce));
	
	
	CH_KeekedComputeRatio();
	int[] keekedComputeRatio = new int[n];
	for(int i = 0;i<n;i++)
		keekedComputeRatio[i]=X[i];
	OFCpopulation.add(ObjectiveFunction(keekedComputeRatio));
	population.add(keekedComputeRatio);
	
	
	double chances = 0.0;
    
    
	System.out.println("OFC de bruteforce : "+ObjectiveFunction(population.get(0)));
	for(int i = 0; i<75; i++) {
		RandomSolution();
		chances = Math.random();
		System.out.println("chances : "+chances);
		if(chances>0.9) 
		{
		IH_ExhaustiveSearch(); // try to add a local search in the generation of the starting population instead of just random solution
		// but gives worse solution, not enough diversity
		}
		int[] randSol = new int[n];
		for(int j = 0;j<n;j++)
			randSol[j]=X[j];
		population.add(randSol);
		OFCpopulation.add(ObjectiveFunction(randSol));
		
	}
	int worstOFC = Collections.min(OFCpopulation);
	int bestOFC = Collections.max(OFCpopulation);
	System.out.println("worst ofc : "+ worstOFC);
	
	
	System.out.println("OFC of the sixth element : "+ObjectiveFunction(population.get(6)));
	System.out.println("OFC of the fourth element : "+ObjectiveFunction(population.get(4)));
	
	method = new Throwable().getStackTrace()[0].getMethodName();
	for(int p=0; p<10000;p++) 
	{
		
	    	int[] child = new int[n];
	    	int[] child2 = new int[n];
	    	int[] parent1 = new int[n];
	    	int[] parent2 = new int[n];
	    	// Chose the parents and genetic operators
	    	int indexP1 = 0;
	    	int indexP2 = 0;
	    	int indexP3 = 0;
	    	int indexP4 = 0;
	        Random rand = new Random();
	        indexP1 = rand.nextInt(population.size());
	        indexP2 = rand.nextInt(population.size());
	        indexP3 = rand.nextInt(population.size());
	        indexP4 = rand.nextInt(population.size());
	        //System.out.println("IndexP1 :"+indexP1);
	        //System.out.println("IndexP2 :"+indexP2);
	    	ArrayList<int[]> children = new ArrayList<int[]>();
			   			
			parent1 = population.get(indexP1);
			parent2 = population.get(indexP2);
			int[] parent3 = population.get(indexP3);
			int[] parent4 = population.get(indexP4);
			
			// Generating two children with the crossover operator
			for(int k = 0; k<n;k++) {
				
				if(k%2==0)
				{
				X[k]=parent1[k];
				}
				if(k%2==1)
				{
				X[k]=parent2[k];
				}
			
	}

			// Local search for the child
			IH_ExhaustiveSearch();
			for(int i = 0;i<n;i++)
				child[i]=X[i];
										
			// Evaluation step
			int z = ObjectiveFunction(child);
   			if(checkConstraintsGeneticAlgorithm(child) && !(OFCpopulation.contains(z))) {
   				//System.out.println("feasible solution found");
   				// we check if z is not already in our population to avoid repeating the same information
   				
   				//System.out.println(z);
   				if(population.size()<300) 
   				{
   					population.add(child);
   					OFCpopulation.add(z);
   					worstOFC = Collections.min(OFCpopulation);
   					
   				}
   				if(population.size()>=300 && z>worstOFC) 
   				{
   				System.out.println("overcrowed");
   				population.add(child);
   				OFCpopulation.add(z);
   				population.remove(OFCpopulation.indexOf(worstOFC));
   				OFCpopulation.remove(OFCpopulation.indexOf(worstOFC));
   				worstOFC = Collections.min(OFCpopulation);
   				
   				if(bestOFC<z) {
   					System.out.println("BETTER SOLUTION FOUND");
   					bestOFC=z;

   				}
			}
			System.out.println(worstOFC);
   			}
			
			
	    	int[] bestX = population.get(OFCpopulation.indexOf(bestOFC));
	    	for(int m = 0;m<n;m++)
	    		X[m]=bestX[m];
	    	System.out.println("p : "+p);
	    	System.out.println("population : "+population.size()); // to check if our population is to big or not
	

	
	}
	
	end = System.nanoTime();  // end of the timer
    elapsedTime = (end - start) / 1000000;   // duration of the algorithm in ms
	 	

}
    protected static int[] ExhaustiveSearch(int[] RX) {
        
        ArrayList<Float> tempArray2 = new ArrayList<Float>(n);
        ArrayList<Float> tempArray3 = new ArrayList<Float>(n);
        for (int i = 0; i < n; i++) {
            int sum = 0;

            for (int j = 0; j < m; j++)
                sum += A[j][i];

            float sum2 = (float) C[i] / sum;

            tempArray3.add(sum2);
            tempArray2.add(sum2);
        }

        //Collections.sort(tempArray3, Collections.reverseOrder());
        Collections.sort(tempArray3);

        int bestS = 0;
        int bestY = 0;

        ArrayList<Integer> OneIndexTable = new ArrayList<Integer>();
        ArrayList<Integer> ZeroIndexTable = new ArrayList<Integer>();

        IndicesLists(OneIndexTable, ZeroIndexTable);

        for (int i = 0; i < n; i++) {
            bestS = -1;
            bestY = -1;
            //System.out.println(tempArray3.get(i));
            int b = tempArray2.indexOf(tempArray3.get(i));
            //System.out.println(b);
            if (RX[b] == 1) {
                for (int s = 0; s < ZeroIndexTable.size() - 1; s++) {
                    for (int y = s + 1; y < ZeroIndexTable.size() - 1; y++) {
                        int valueOfS = ZeroIndexTable.get(s);
                        int valueOfY = ZeroIndexTable.get(y);
                        if (C[b] < C[valueOfS] + C[valueOfY]) {
                            RX[b] = 0;
                            RX[valueOfS] = RX[valueOfY] = 1;
                            if (checkConstraints2(b, valueOfS, valueOfY)) {

                                bestS = valueOfS;
                                bestY = valueOfY;
                            }
                            RX[b] = 1;
                            RX[valueOfS] = RX[valueOfY] = 0;
                        }
                    }
                }
                if (bestS != -1) {
                    RX[bestS] = RX[bestY] = 1;
                    RX[b] = 0;
                    ZeroIndexTable.add(b);
                    ZeroIndexTable.remove(ZeroIndexTable.indexOf(bestS));
                    ZeroIndexTable.remove(ZeroIndexTable.indexOf(bestY));
                    for (int t = 0; t < m; t++)
                        G[t] = G[t] - A[t][b] + A[t][bestS] + A[t][bestY];
                }
            }
        }

        end = System.nanoTime();  // end of the timer
        elapsedTime = (end - start) / 1000000;   // duration of the algorithm
        
        return RX;
    }

    
    protected static void MemeticAlgorithm() {
    	
    	
    	start = System.nanoTime();
    	ArrayList<int[]> population = new ArrayList<int[]>();
    	ArrayList<Integer> OFCpopulation = new ArrayList<Integer>(); 
  
    	// Generate starting population
    	BruteForce();
    	int[] bruteForce = new int[n];
    	for(int i = 0;i<n;i++)
    		bruteForce[i]=X[i];
    	population.add(bruteForce);
    	OFCpopulation.add(ObjectiveFunction(bruteForce));
    	
    	
    	/*CH_KeekedComputeRatio();
    	int[] keekedComputeRatio = new int[n];
    	for(int i = 0;i<n;i++)
    		keekedComputeRatio[i]=X[i];
    	OFCpopulation.add(ObjectiveFunction(keekedComputeRatio));
    	population.add(keekedComputeRatio);
    	int bestOFC = ObjectiveFunction(keekedComputeRatio);*/
    	
    	double chances = 0.0;
        
        
    	System.out.println("OFC de bruteforce : "+ObjectiveFunction(population.get(0)));
    	for(int i = 0; i<75; i++) {
    		RandomSolution();
    		chances = Math.random();
    		System.out.println("chances : "+chances);
    		if(chances>0.9) 
    		{
    		IH_ExhaustiveSearch(); // try to add a local search in the generation of the starting population instead of just random solution
    		// but gives worse solution, not enough diversity
    		}
    		int[] randSol = new int[n];
    		for(int j = 0;j<n;j++)
    			randSol[j]=X[j];
    		population.add(randSol);
    		OFCpopulation.add(ObjectiveFunction(randSol));
    		
    	}
    	int worstOFC = Collections.min(OFCpopulation);
    	int bestOFC = Collections.max(OFCpopulation);
    	System.out.println("worst ofc : "+ worstOFC);
    	
    	
    	System.out.println("OFC of the sixth element : "+ObjectiveFunction(population.get(6)));
    	System.out.println("OFC of the fourth element : "+ObjectiveFunction(population.get(4)));
    	
    	method = new Throwable().getStackTrace()[0].getMethodName();
    	for(int p=0; p<10000;p++) 
    	{
    		
		    	int[] child = new int[n];
		    	int[] child2 = new int[n];
		    	int[] parent1 = new int[n];
		    	int[] parent2 = new int[n];
		    	// Chose the parents and genetic operators
		    	int indexP1 = 0;
		    	int indexP2 = 0;
		        Random rand = new Random();
		        indexP1 = rand.nextInt(population.size());
		        indexP2 = rand.nextInt(population.size());
		        //System.out.println("IndexP1 :"+indexP1);
		        //System.out.println("IndexP2 :"+indexP2);
		    	ArrayList<int[]> children = new ArrayList<int[]>();
    			   			
    			parent1 = population.get(indexP1);
    			parent2 = population.get(indexP2);
    			
    			// Generating two children with the crossover operator
    			for(int k = 0; k<n/2;k++) {
    				
    					X[k]=parent1[k];
    					//child2[k]=parent2[k];
    					//System.out.println("child2 k coefficients coming from parent 2 : "+child2[k]);
    			}
    			for(int k = n/2; k<n;k++) {
    				
						X[k]=parent2[k];
					//child2[k]=parent1[k];
					//System.out.println("child2 k coefficients coming from parent 2 : "+child2[k]);
			}

    			// Local search for the child
    			IH_ExhaustiveSearch();
    			for(int i = 0;i<n;i++)
    				child[i]=X[i];

    			
    			
    			
    		
    			// Evaluation step
    			int z = ObjectiveFunction(child);
       			if(checkConstraintsGeneticAlgorithm(child) && !(OFCpopulation.contains(z))) {
       				//System.out.println("feasible solution found");
       				// we check if z is not already in our population to avoid repeating the same information
       				
       				//System.out.println(z);
       				if(population.size()<300) 
       				{
       					population.add(child);
       					OFCpopulation.add(z);
       					worstOFC = Collections.min(OFCpopulation);
       					
       				}
       				if(population.size()>=300 && z>worstOFC) 
       				{
       				System.out.println("overcrowed");
       				population.add(child);
       				OFCpopulation.add(z);
       				population.remove(OFCpopulation.indexOf(worstOFC));
       				OFCpopulation.remove(OFCpopulation.indexOf(worstOFC));
       				worstOFC = Collections.min(OFCpopulation);
       				
       				if(bestOFC<z) {
       					System.out.println("BETTER SOLUTION FOUND");
       					bestOFC=z;

       				}
    			}
    			System.out.println(worstOFC);
       			}
    			
    			
		    	int[] bestX = population.get(OFCpopulation.indexOf(bestOFC));
		    	for(int m = 0;m<n;m++)
		    		X[m]=bestX[m];
		    	System.out.println("p : "+p);
		    	System.out.println("population : "+population.size()); // to check if our population is to big or not
    	
   
    	
    	}
    	
    	end = System.nanoTime();  // end of the timer
        elapsedTime = (end - start) / 1000000;   // duration of the algorithm in ms
    	 	
   
    }

    protected static void TestHeuristics(String baseName) throws IOException {
        // processing files with data
     for (int i = 1; i <= 5; i++) {
            fileName = baseName + i + ".txt";
            ReadData(fileName);

            File f = new File("result.txt");
            FileWriter fw = new FileWriter(f, true);
            fw.write("==================================\n>>>> " + fileName + " <<<<\n==================================\n");
            fw.close();


/////////////////////////////////////  IH_RandomizedComputeRatio() ////////////////////////////////////////////////

/*
            CH_ComputeRatio();
            PrintResult();
            IH_RandomizedComputeRatio();
            PrintResult();

            CH_KeekedComputeRatio();
            PrintResult();
            IH_RandomizedComputeRatio();
            PrintResult();

///////////////////////////////////////////  IH_MixedComputeRatio() ////////////////////////////////////////////////


            CH_ComputeRatio();
            PrintResult();
            IH_MixedComputeRatio();
            PrintResult();

            CH_KeekedComputeRatio();
            PrintResult();
            IH_MixedComputeRatio();
            PrintResult();
///////////////////////////////////////////  IH_ExhaustiveSearch() ////////////////////////////////////////////////

            CH_ComputeRatio();
            PrintResult();
            IH_ExhaustiveSearch();
            PrintResult();

            CH_KeekedComputeRatio();
            PrintResult();
            IH_ExhaustiveSearch();
            PrintResult();  */
            
            GeneticAlgorithmV2();
            PrintResult();
            
            //RandomSolution();
            //PrintResult();
        } 
    }
    public static void main(String[] args) throws IOException {
        // reset the file
        File f = new File("result.txt");
        FileWriter fw = new FileWriter(f);
        fw.close();

       // Test on a specific instance of the problem
        TestHeuristics("500-30-0");
        
       
			
    }

}
