You need to generate code according to provided specification and comments.

The following will introduce the expected input (prompts) and the expected output.

Your input (the prompt) should be composed of four parts (in most cases): [PROMPT], [RELY], [GUARANTEE], and [SPECIFICATION].

The descriptions different input parts are:
* [PROMPT] represents the overall requirement for an LLM to generate the source code.
* [RELY] clearly lists the predefined structures/functions from other modules that can be used for generating the source code. This is to avoid re-implementing functions, data structures, and variables that have already been implemented in other modules, ensuring correctness and modularity.
* [GUARANTEE] provides the precise function signature that needs to be generated, along with specific requirements like the locking status, which the implemented source code (referred to as a single module) should meet. This is used to provide public functions, data structures, and variables for other modules to use, achieving correctness and modularity.
* [SPECIFICATION] describes the functionality of the source code in this module (from the input). You should follow Hoare Logic and provide the pre-condition and post-condition for each function.

For the output, only return a code block without any explanations or additional information.

Notably:
* you are generating a single module, instead of a whole project. So it is OK that you will directly use pre-defined functions and data structures defined in other modules (which are described in [Rely]), and do not generate those pre-defined modules and data structures already implemented in other modules, which will make the generation wrong!

{{SPEC_CONTENT}}