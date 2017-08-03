Amoeba: Binary Code Diverisfication through Composite Software Diversification


# Installation

Amoeba is built on top of Uroboros, for installation instruction, please refer
to *RAEDME_uroboros.md*.

# Usage

Amoeba takes 32-bit ELF executable binaries as the input. Currently we provide
*ten* classic diversification transformations. Users can select one or multiple
methods to use. The diversification code is at ./src/plugins/diversification.
For implementing new diversification transformation, please refer to *README_uroboros.md*.

We have set up code to invoke the diversification transformations in src/ail.ml.
Users can directly leverage the code there for instrumentation.

For example, in order to utilize basic block reordering for instrumentation,
uncomment code in ail.ml at line 197:

     let il' = bb_rod_div#visit il'

After that, rebuild the codebase through

    cd src
    ./build

To use Amoeba to diversify bzip:

    python amoeba.py bzip


Note that multiple transformations can be used together in one iteration. In that case, 
users can uncomment multiple transformation code in ail.ml. 

We also provide a helper function get_random_num() in ail.ml to generate a random number. To randomly select different 
transformation passes in different iterations, users can leverage a random number 
to decide which transformation to choose 
(For instance, only use basic block reordering when random_number mod 9 == 0).


As tested in our paper, the diversification process can be iterated for
multiple times. Python script amoeba.py provides an option (-i) to manipulate 
the diverisfication process. For example, the following command iterates the diversification transformations for 500 times.

    python amoeba.py bzip -i 500


After transformtion, a subfolder will be created in ./src folder, with input binary name and
timestamp. For example:

    test_fold_bzip_2017-04-02_11:11:50

When reassembling the diversified outputs, Ameoba requires to use linker
scripts to leave "enough space" for the outputs (as the size of diversified
code can probably grow).

For instance, if originally the *.text* section of bzip is loaded into memory address 0x8048440. 
As the instrumented code size grows, users can conservatively load the *.text* section into 
address 0x7048000 to leave additional memory space.

Please refer to *README_uroboros.md* for how to write linker scripts.
# Amoeba
