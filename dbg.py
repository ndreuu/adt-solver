
import os
import sys
import shutil

def main():
    args = sys.argv[1:]
    directory = os.path.join(args[0], "dbg")
    # if os.path.exists(directory):
        # shutil.rmtree(directory)
    # os.makedirs(directory)



    horn_input_path = os.path.join(directory, "horn-input.smt2") 
    redlog_input_path = os.path.join(directory, "redlog-input.smt2")
    redlog_output_path = os.path.join(directory, "redlog-output.smt2")
    smt_input_path = os.path.join(directory, "smt-input.smt2")
    proof_path = os.path.join(directory, "proof.smt2")

    def splited(path: str) -> list[str]:
        with open(path) as f:
            content = f.read()

        return content.split('--------------------')


    states: list[tuple] = list(zip(
        splited(horn_input_path), 
        splited(redlog_input_path), 
        splited(redlog_output_path), 
        splited(smt_input_path),
        splited(proof_path)))

    for i in range(len(states)):
        os.mkdir(os.path.join(directory, i.__str__()))

    for i in range(len(states)):
        state_path = os.path.join(directory, i.__str__()) 
        with open(os.path.join(state_path, 'horn-input.smt2'), 'w') as f:
            f.write(states[i][0])
        with open(os.path.join(state_path, 'redlog-input.red'), 'w') as f:
            f.write(states[i][1])
        with open(os.path.join(state_path, 'redlog-output.smt2'), 'w') as f:
            f.write(states[i][2])
        with open(os.path.join(state_path, 'smt-input.smt2'), 'w') as f:
            f.write(states[i][3])
        with open(os.path.join(state_path, 'proof.smt2'), 'w') as f:
            f.write(states[i][4])

    os.remove(horn_input_path)
    os.remove(redlog_input_path)
    os.remove(redlog_output_path)
    os.remove(smt_input_path)
    os.remove(proof_path)


if __name__ == "__main__":
    main()
