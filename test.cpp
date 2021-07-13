#include <iostream>
#include <fstream>
#include <vector>
#include <boost/algorithm/string.hpp> 
#include <unordered_map>
#include <bits/stdc++.h> 
#include <iomanip>
#include <algorithm>
#include <queue>
#include <sstream>

using namespace std;
using namespace boost;

uint32_t DRAM[1024][256];
uint32_t Row_buffer[256];
uint32_t row_buffer_counter;
uint32_t cycle;
int MRM_cycles = 5;
int total_mrm = 0;
bool DRAM_busy = false;
int required_clock;
int internal_clock;
int curr_row;
int32_t Row_number = -1;

class Core
{
    public :
        string Registers[32];
        uint32_t RegisterValues[32];
        string InstructionSet[10];
        string current_instruction;
        uint32_t PC;
        uint32_t number_of_instructions;
        vector<string> Input_program;
        unordered_map<string, uint32_t> register_map;
        unordered_map<string, uint32_t> pendingLabel;
        unordered_map<string, uint32_t> Label_address;
        unordered_map<uint32_t, tuple <string, uint32_t, uint32_t>> RequestManager;
        unordered_map<uint32_t, bool> dram_request;
        unordered_map<uint32_t, bool> completed;
        unordered_map<uint32_t, bool> conflict;
        uint32_t Memory[2000];
        queue<uint32_t> instr_buffer;
        uint32_t dram_register;
        int dram_access;
        bool last_set;
        bool dram_execute;
        bool buffer_execute;
        int last;
        int halt;
        int total;
        uint32_t ROW_ACCESS_DELAY;
        uint32_t COL_ACCESS_DELAY;
        uint32_t line_num;
        uint32_t Total_instructions;
        uint32_t get_register(string reg);
        void performSw(uint32_t val, uint32_t address, int i);
        void performLw(uint32_t reg, uint32_t address, int i);
        void displayState();
        void remove_spaces(string &str);
        uint32_t ParseInstruction(string instruction);
        uint32_t get_encoded(string instr_segment[]);
        void ExecuteInstruction(uint32_t opcode, int i);
        string binary (int decimal);
        uint32_t decimal(string bin);
        Core(string filename);
        void Storing();
        void Execute(int i);
};

Core::Core (string filename)
{
    string register_names[] = {"$zero", "$at", "$v0", "$v1", "$a0", "$a1", "$a2", "$a3", "$t0", "$t1", "$t2", 
    "$t3", "$t4", "$t5", "$t6", "$t7", "$s0", "$s1", "$s2", "$s3", "$s4", "$s5", "$s6", "$s7", "$t8", "$t9", 
    "$k0", "$k1", "$gp", "$sp", "$fp", "$ra"};

    string instruction_names[] = {"add", "sub", "mul", "beq", "bne", "slt", "j", "lw", "sw", "addi"};

    number_of_instructions = 0;
    line_num = 0;
    PC = 0;
    ROW_ACCESS_DELAY = 10;
    COL_ACCESS_DELAY = 2;
    Total_instructions = 0;
    halt = 0;
    dram_execute = false;
    buffer_execute = false;
    total = 0;
    
    for (int i = 0; i < 32; i++)
    {
        Registers[i] = register_names[i];
        RegisterValues[i] = 0;
        register_map[register_names[i]] = i;
        conflict[i] = false;
    }

    ifstream fin (filename);
    if (!fin.is_open())
    {
        cout << "Error: The filename you entered does not exist or could not be opened." <<endl;
        exit(1);
    }

    string instruction;
    
    while(getline(fin, instruction))
    {
        number_of_instructions += 1;
        Input_program.push_back(instruction);
    }
    fin.close();
}

void Core::remove_spaces(string &str)
{
    uint32_t j = 0;
	while (j<str.size() && (str[j]==' ' || str[j]=='\t')) 
	{
		j++;
	}
	str = str.substr(j); 
}

void Core::displayState()
{
    cout << "------------------------" << endl;
    cout << "Register" << "   " << "Stored values" << endl;
    for (int i = 0; i < 32; i++) {
        cout << Registers[i] << "     " << hex << "0x" << RegisterValues[i]  << endl; 
    }
    cout << setbase(10) << endl;
}

string Core::binary(int decimal) 
{
    string bin = "";
    for (int i = 31; i >= 0; i--) {
        int k = decimal >> i;
        if (k & 1) {
            bin = bin + "1";
        }
        else {
            bin = bin + "0";
        }
    }
    return bin;
}

uint32_t Core::decimal(string bin)
{
    uint32_t deci = 0;
    string num = bin;
    int base = 1;
    int len = num.length();
    for (int i = len-1; i >= 0; i--) {
        if (num[i] == '1') {
            deci = deci + base;
        }
        base = base*2;
    }
    return deci;
}
void Core::Storing()
{
    while (line_num < number_of_instructions)
    {
        current_instruction = Input_program[line_num];
        remove_spaces(current_instruction);
        if (current_instruction == "") 
        {
            line_num = line_num + 1;
            continue;
        }
        uint32_t opcode = ParseInstruction(Input_program[line_num]);
        line_num += 1;
    }
    for (auto label_map: pendingLabel)
    {
        string label = label_map.first;
        uint32_t address = label_map.second;
        if (Label_address[label])
        {
            uint32_t instruction = Memory[address];
            Memory[address] = instruction + Label_address[label];
        }
        else
        {
            cout << "Error: Label declaration not found for " + label << endl;
            exit(1);
        }
    }
    Total_instructions = PC;
    PC = 0;
}

uint32_t Core::get_encoded (string instr_segment[]) 
{
    if (instr_segment[0] == "j")
    {
        uint32_t op_id = 2;
        string label = instr_segment[1];
        uint32_t address;
        if (Label_address[label]) {
            address = Label_address[label];
        }
        else {
            //if the label is not declared yet

            uint32_t code = op_id << 26;
            pendingLabel[label] = PC;
            address = 0;
        }
        
        uint32_t code = (op_id << 26) + address;
        return code;
    }
    else if (instr_segment[0] == "add") {
        uint32_t op_code = 0;
        uint32_t dst_reg = get_register(instr_segment[1]);
        uint32_t src1 = get_register(instr_segment[2]);
        uint32_t src2 = get_register(instr_segment[3]);
        uint32_t shamt = 0;
        uint32_t func_code = 32;
        uint32_t code = (op_code << 26) + (dst_reg << 21) + (src1 << 16) + (src2 << 11) + (shamt << 6) + func_code;
        return code;
    }
    else if  (instr_segment[0] == "sub") {
        uint32_t op_code = 0;
        uint32_t dst_reg = get_register(instr_segment[1]);
        uint32_t src1 = get_register(instr_segment[2]);
        uint32_t src2 = get_register(instr_segment[3]);
        uint32_t shamt = 0;
        uint32_t func_code = 34;

        uint32_t code = (op_code << 26) + (dst_reg << 21) + (src1 << 16) + (src2 << 11) + (shamt << 6) + func_code;
        return code;
    }
    else if  (instr_segment[0] == "mul") {
        uint32_t op_code = 0;
        uint32_t dst_reg = get_register(instr_segment[1]);
        uint32_t src1 = get_register(instr_segment[2]);
        uint32_t src2 = get_register(instr_segment[3]);
        uint32_t shamt = 0;
        uint32_t func_code = 24;

        uint32_t code = (op_code << 26) + (dst_reg << 21) + (src1 << 16) + (src2 << 11) + (shamt << 6) + func_code;
        return code;
    }
    else if (instr_segment[0] == "slt") {
        uint32_t op_code = 0;
        uint32_t reg1 = get_register(instr_segment[1]);
        uint32_t reg2 = get_register(instr_segment[2]);
        uint32_t reg3 = get_register(instr_segment[3]);
        uint32_t shamt = 0;
        uint32_t func_code = 42;

        uint32_t code = (op_code << 26) + (reg1 << 21) + (reg2 << 16) + (reg3 << 11) + (shamt << 6) + func_code;
        return code;
    }
    else if  (instr_segment[0] == "beq") {
        uint32_t op_code = 4;
        uint32_t reg1 = get_register(instr_segment[1]);
        uint32_t reg2 = get_register(instr_segment[2]);
        uint32_t address;
        string label = instr_segment[3];
        if (Label_address[label]) {
            address = Label_address[label];
        }
        else {
            uint32_t code = op_code << 26;
            address = 0;
            pendingLabel[label] = PC;
        }
        uint32_t code = (op_code << 26) + (reg1 <<21) + (reg2 << 16) + address;
        return code;

    }
    else if  (instr_segment[0] == "bne") {
        uint32_t op_code = 5;
        uint32_t reg1 = get_register(instr_segment[1]);
        uint32_t reg2 = get_register(instr_segment[2]);
        uint32_t address ;
        string label = instr_segment[3];
        if (Label_address[label]) {
            address = Label_address[label];
        }
        else {
            uint32_t code = op_code << 26;
            address = 0;
            pendingLabel[label] = PC;
        }
        uint32_t code = (op_code<<26) + (reg1 <<21) + (reg2 << 16) + address;
        return code;
    }
    else if  (instr_segment[0] == "addi") {
        uint32_t op_code = 8;
        uint32_t src_reg = get_register(instr_segment[2]);
        uint32_t dst_reg = get_register(instr_segment[1]);
        uint32_t num = stoi(instr_segment[3]);
        uint32_t code = (op_code << 26) + (src_reg << 21) + (dst_reg << 16) + num;
        return code;
    }
    else if (instr_segment[0] == "lw") {
        uint32_t op_code = 35;
        uint32_t src_reg = get_register(instr_segment[3]);
        uint32_t dst_reg = get_register(instr_segment[1]);
        uint32_t offset = stoi(instr_segment[2]);
        uint32_t code = op_code * uint32_t(pow(2,26)+0.5) + dst_reg * uint32_t(pow(2,21)+0.5) + src_reg  * uint32_t(pow(2,16)+0.5) + offset;
        return code;
    }
    else if  (instr_segment[0] == "sw") {
        uint32_t op_code = 43;
        uint32_t dst_reg = get_register(instr_segment[3]);
        uint32_t src_reg = get_register(instr_segment[1]);
        uint32_t offset = stoi(instr_segment[2]);
        uint32_t code = op_code * uint32_t(pow(2,26)+0.5) + dst_reg * uint32_t(pow(2,21)+0.5) + src_reg  * uint32_t(pow(2,16)+0.5) + offset;
        return code;
    }
    else {
        return -1;
    }
}

uint32_t Core::get_register (string reg) {
    
    if (register_map[reg] >= 0) {
        if (reg == "$fp" || reg == "$sp" || reg == "$gp") {
            cout << "Error: Can't use $fp, $sp or $gp registers." << endl;
            exit(1);
        }
        else {
            return register_map[reg];
        }
    }
    else {
        cout << "Error: Not a valid register." << endl;
        exit(1);
    }
}

uint32_t Core::ParseInstruction(string instruction)
{
    string instr = instruction;
    remove_spaces(instr);

    //check for label
    if (instr.find(":") != -1)
    {
        
        uint32_t j = 0;
        string label = "";
        while (j < instr.length())
        {
            if (instr[j] == ':' || instr[j] == ' ' || instr[j] == '\t')
            {
                break;
            }
            else
            {
                label = label + instr[j];
                j++;
            }
        }

        instr = instr.substr(j);

        remove_spaces(instr);
        
        if (instr[0] == ':')
        {
            instr = instr.substr(1);

            remove_spaces(instr);
            
            //if the label already exists
            if (Label_address[label])
            {
                cout << "Error: Same Label declared twice" << endl;
                exit(1);
            }

            //considering only type label : instruction
            Label_address[label] = PC;
            uint32_t opcode = ParseInstruction(instr);
            return opcode;
        }
        else 
        {
            cout << "Error: Unknown string before label" << endl;
            exit(1);
        }
    }

    //insruction set instructions
    string cmd;
    int j = 0;
    while (j < instr.length())
    {
        if (instr[j] != ' ' && instr[j] != '\t')
        {
            cmd = cmd + instr[j];
            j = j + 1;
        }
        else
        {
            break;
        }
    }
    instr = instr.substr(j);

    if (cmd == "j")
    {
        string instruction_segments[2];
        instruction_segments[0] = "j";

        remove_spaces(instr);

        if (instr == "")
        {
            cout << "Error: Expected a label name" << endl;
            exit(1);
        }
        else
        {
            string label_name = "";
            uint32_t j = 0; 
            while (j < instr.length() && instr[j] != ' ' && instr[j] != '\t') {
                label_name = label_name + instr[j];
                j = j + 1;
            }

            instruction_segments[1] = label_name;
            uint32_t operation_id = get_encoded(instruction_segments);
            Memory[PC] = operation_id;
            PC = PC + 1;
            return operation_id;
        }
    }
    else if (cmd == "sw" || cmd == "lw")
    {
        string instruction_segments[4];
        instruction_segments[0] = cmd;

        remove_spaces(instr);

        //first register detect
        string name1 = instr.substr(0,3);
        
        instruction_segments[1] = name1;
        instr = instr.substr(3);

        remove_spaces(instr);
        //removing comma
        instr = instr.substr(1);
        
        remove_spaces(instr);

        uint32_t j = 0;
        string num = "0";
        while (j < instr.length() && instr[j] != ' ' && instr[j] != '\t')
        {
            if (instr[j] == '(')
            {
                break;
            }
            else
            {
                num = num + instr[j];
                j = j + 1;
            }
        }
        
        instruction_segments[2] = num;
        instr = instr.substr(j);
        remove_spaces(instr);
        
        if (instr[0] == '(')
        {
            instr = instr.substr(1);
            remove_spaces(instr);
            string name2 = "";
            int j = 0;

            while (instr[j] != ')')
            {
                name2 = name2 + instr[j];
                j = j + 1;
            }

            instruction_segments[3] = name2;
            uint32_t operation_id = get_encoded(instruction_segments);
            Memory[PC] = operation_id;
            PC = PC + 1;
            return operation_id;
        }
        else
        {
            cout << "Expected a parenthesis..." << endl;
            exit(1);
        }
        
    }
    else
    {
        string instruction_segments[4];
        instruction_segments[0] = cmd;
        stringstream stream(instr);
        j = 1;
        while (stream.good())
        {
            string substr;
            getline(stream, substr, ',');
            remove_spaces(substr);
            instruction_segments[j] = substr;
            j = j + 1;
        }
        uint32_t operation_id = get_encoded(instruction_segments);
        Memory[PC] = operation_id;
        PC = PC + 1;
        return operation_id;

    }
}

void Core::ExecuteInstruction(uint32_t opcode, int i)
{
    uint32_t dec = opcode ;
    string bin = binary(dec);
    string op_id = bin.substr(0,6);

    if (op_id == "000000")
    {
        bin = bin.substr(6);
        string func_code = bin.substr(bin.length()-6, 6);

        int dest = decimal(bin.substr(0,5));
        int src1 = decimal(bin.substr(5,5));
        int src2 = decimal(bin.substr(10,5));

        if (!conflict[dest] && !conflict[src1] && !conflict[src2])
        {
            if (func_code == "100000") //add 32
            {
                int32_t src1value = RegisterValues[src1];
                int32_t src2value = RegisterValues[src2];
                RegisterValues[dest] = src1value + src2value;
                cout << "Cycle " << cycle << " Core " << i << ": Executed instruction " << PC << endl;
                completed[PC] = true;
                PC = PC + 1;
                total += 1;
            }
            else if (func_code == "100010") //sub 34
            {
                int32_t src1value = RegisterValues[src1];
                int32_t src2value = RegisterValues[src2];
                RegisterValues[dest] = src1value - src2value;
                cout << "Cycle " << cycle << " Core " << i << ": Executed instruction " << PC << endl;
                completed[PC] = true;
                PC = PC + 1;
                total += 1;
            }
            else if (func_code == "011000")   //mul 24
            {
                int32_t src1value = RegisterValues[src1];
                int32_t src2value = RegisterValues[src2];
                RegisterValues[dest] = src1value*src2value;
                cout << "Cycle " << cycle << " Core " << i << ": Executed instruction " << PC << endl;
                completed[PC] = true;
                PC = PC + 1;
                total += 1;
            }
            else if (func_code == "101010")   //slt 42
            {
                int32_t src1value = RegisterValues[src1];
                int32_t src2value = RegisterValues[src2];

                if(src1value < src2value)
                {
                    RegisterValues[dest] = 1;
                }
                else
                {
                    RegisterValues[dest] = 0;
                }
                cout << "Cycle " << cycle << " Core " << i << ": Executed instruction " << PC << endl;
                completed[PC] = true;
                PC = PC + 1;
                total += 1;
            }
        }
        else
        {
            halt = 1;
        }
    }
    else if (op_id == "001000")     //addi 8
    {
        
        bin = bin.substr(6);
        int src = decimal(bin.substr(0,5));
        int dest = decimal(bin.substr(5,5));
        if (!conflict[src] && !conflict[dest])
        {
            uint32_t num = decimal(bin.substr(10));
            RegisterValues[dest] = RegisterValues[src] + num;
            cout << "Cycle " << cycle << " Core " << i << ": Executed instruction " << PC << endl;
            completed[PC] = true;
            PC = PC + 1;
            total += 1;
        }
        else
        {
            halt = 1;
        }
    }
    else if (op_id == "000100")    //beq 4
    {
        if (!DRAM_busy)
        {
            bin = bin.substr(6);
            int src1 = decimal(bin.substr(0,5));
            int src2 = decimal(bin.substr(5,5));
            if (!conflict[src1] && !conflict[src2])
            {
                int32_t src1value = RegisterValues[src1];
                int32_t src2value = RegisterValues[src2];
                cout << "Cycle " << cycle << " Core " << i << ": Executed instruction " << PC << endl;
                completed[PC] = true;
                total += 1;
                if(src1value==src2value)
                {
                    PC = decimal(bin.substr(10));
                }
                else
                {
                    PC = PC + 1;
                }
            }
            else
            {
                halt = 1;
            }
        }
        else
        {
            halt = 1;
        }
        
    }
    else if (op_id == "000101")   //bne 5
    {
        if (!DRAM_busy)
        {
            bin = bin.substr(6);
            int src1 = decimal(bin.substr(0,5));
            int src2 = decimal(bin.substr(5,5));
            if (!conflict[src1] && !conflict[src2])
            {
                int32_t src1value = RegisterValues[src1];
                int32_t src2value = RegisterValues[src2];

                cout << "Cycle " << cycle << " Core " << i << ": Executed instruction " << PC << endl;
                completed[PC] = true;
                total += 1;
                if(src1value!=src2value)
                {
                    PC = decimal(bin.substr(10));
                }
                else
                {
                    PC = PC + 1;
                }
                
            }
            else
            {
                halt = 1;
            }
        }
        else
        {
            halt = 1;
        }
        
    }
    else if (op_id == "000010")     //j 2
    {
        if (!DRAM_busy)
        {
            bin = bin.substr(6);
            uint32_t address = decimal(bin.substr(0));
            PC = address;
            cout << "Cycle " << cycle << " Core " << i << ": Executed instruction " << PC << endl;
            completed[PC] = true;
            total += 1;
        }
        else
        {
            halt = 1;
        }
    }

    else if (op_id == "100011")     //lw 35
    {
        bin = bin.substr(6);
        uint32_t dest = decimal(bin.substr(0,5));
        uint32_t src = decimal(bin.substr(5,5));
        uint32_t offset = decimal(bin.substr(10));
        uint32_t curr_address = RegisterValues[src] + offset;

        if (curr_address%4 != 0) 
        {
            cout << "Error: Can't access this memory" << endl;
            exit(1);
        }

        uint32_t row = curr_address/1024;
        uint32_t col = curr_address - 1024*row;
        col = col/4;

        if ((!conflict[src] && !conflict[dest]) || dram_execute)
        {

            if (!DRAM_busy || dram_execute)
            {
                if (!dram_request[PC])
                {
                    //instantaneous request
                    dram_request[PC] = true;
                    cout << "Cycle " << cycle << " Core " << i << ": DRAM request raised for instruction " << PC << endl;
                    dram_register = dest;
                    conflict[dest] = true;
                    RequestManager[PC] = make_tuple("lw", dest, curr_address);
                    DRAM_busy = true;
                    if (Row_number == -1)
                    {
                        curr_row = row;
                        required_clock = COL_ACCESS_DELAY + ROW_ACCESS_DELAY;
                        cout << "Cycle " << cycle+1 << "-" << cycle + ROW_ACCESS_DELAY << " Row number " << row << " being copied to the Row buffer" << endl;
                        cout << "Cycle " << cycle + ROW_ACCESS_DELAY + 1 << "-" << cycle + ROW_ACCESS_DELAY + COL_ACCESS_DELAY << " Column number " << col << " being fetched" << endl;
                    }

                    else if (row == Row_number)
                    {
                        required_clock = COL_ACCESS_DELAY;
                        cout << "Cycle " << cycle + 1 << "-" << cycle + COL_ACCESS_DELAY << " Column number " << col << " being fetched" << endl;
                        curr_row = row;
                    }
                    else
                    {
                        required_clock = 2*ROW_ACCESS_DELAY + COL_ACCESS_DELAY;
                        cout << "Cycle " << cycle+1 << "-" << cycle + ROW_ACCESS_DELAY << " Row buffer " << "being copied to the DRAM" << endl; 
                        cout << "Cycle " << cycle+1 + ROW_ACCESS_DELAY << "-" << cycle + 2 * ROW_ACCESS_DELAY << " Row number " << row << " being copied to the Row buffer" << endl; 
                        cout << "Cycle " << cycle + 2*ROW_ACCESS_DELAY + 1 << "-" << cycle + 2*ROW_ACCESS_DELAY + COL_ACCESS_DELAY << " Column number " << col << " being fetched" << endl;
                        curr_row = row;
                    }
                }
                else if (dram_request[PC] && dram_execute)
                {
                    //dram request is already raised
                    tuple<string, uint32_t, uint32_t> tup = RequestManager[PC];
                    performLw(get<1>(tup), get<2>(tup), i);
                    conflict[get<1>(tup)] = false;
                }
                else
                {
                    tuple<string, uint32_t, uint32_t> tup = RequestManager[PC];
                    conflict[get<1>(tup)] = true;
                    DRAM_busy = true;
                    if (Row_number == -1)
                    {
                        curr_row = row;
                        required_clock = COL_ACCESS_DELAY + ROW_ACCESS_DELAY;
                        cout << "Cycle " << cycle << "-" << cycle + ROW_ACCESS_DELAY-1 << " Row number " << row << " being copied to the Row buffer" << endl;
                        cout << "Cycle " << cycle + ROW_ACCESS_DELAY << "-" << cycle -1 + ROW_ACCESS_DELAY + COL_ACCESS_DELAY << " Column number " << col << " being fetched" << endl;
                    }

                    else if (row == Row_number)
                    {
                        required_clock = COL_ACCESS_DELAY;
                        cout << "Cycle " << cycle  << "-" << cycle-1+COL_ACCESS_DELAY << " Column number " << col << " being fetched" << endl;
                        curr_row = row;
                    }
                    else
                    {
                        required_clock = 2*ROW_ACCESS_DELAY + COL_ACCESS_DELAY;
                        cout << "Cycle " << cycle << "-" << cycle + ROW_ACCESS_DELAY-1 << " Row buffer " << "being copied to the DRAM" << endl; 
                        cout << "Cycle " << cycle + ROW_ACCESS_DELAY << "-" << cycle-1 + 2 * ROW_ACCESS_DELAY << " Row number " << row << " being copied to the Row buffer" << endl; 
                        cout << "Cycle " << cycle + 2*ROW_ACCESS_DELAY << "-" << cycle -1 + 2*ROW_ACCESS_DELAY + COL_ACCESS_DELAY<< " Column number " << col << " being fetched" << endl;
                        curr_row = row;
                    }
                }
            }
            else
            {
                //raising dram request in case some other core is busy
                
                if (row == curr_row)
                {
                    if (instr_buffer.size() < 3)
                    {
                        instr_buffer.push(PC);
                    }
                }
                else
                {
                    if (!last_set)
                    {
                        last = PC;
                        last_set = true;
                    }
                }
                if (!dram_request[PC])
                {
                    dram_request[PC] = true;
                    RequestManager[PC] = make_tuple("lw", dest, curr_address);
                    conflict[dest] = true;
                    cout << "Cycle " << cycle << " Core " << i << ": DRAM request raised for instruction " << PC << endl;
                }
            }
            PC = PC + 1;
        }
        else
        {
            halt = 1;
        }
    }
    else if (op_id == "101011")     //sw 43
    {
        bin = bin.substr(6);
        uint32_t dest = decimal(bin.substr(0,5));
        uint32_t src =  decimal(bin.substr(5,5));
        uint32_t offset = decimal(bin.substr(10));

        uint32_t curr_address = RegisterValues[dest] + offset;
        if (curr_address%4 != 0) 
        {
            cout << "Error: Can't access this memory" << endl;
            exit(1);
        }

        uint32_t row = curr_address/1024;
        uint32_t col = curr_address - 1024*row;
        
        col = col/4;
        
        if (!conflict[src] && !conflict[dest])
        {
            if (!DRAM_busy || dram_execute)
            {
                if (!dram_request[PC])
                {
                    //instantaneous request
                    dram_request[PC] = true;
                    cout << "Cycle " << cycle <<  " Core " << i << ": DRAM request raised for instruction " << PC << endl;
                    DRAM_busy = true;
                    uint32_t val = RegisterValues[src];
                    RequestManager[PC] = make_tuple("sw", val, curr_address);
                    if (Row_number == -1)
                    {
                        curr_row = row;
                        required_clock = COL_ACCESS_DELAY + ROW_ACCESS_DELAY;
                        cout << "Cycle " << cycle+1 << "-" << cycle + ROW_ACCESS_DELAY << " Row number " << row << " being copied to the Row buffer" << endl; 
                        cout << "Cycle " << cycle + ROW_ACCESS_DELAY + 1 << "-" << cycle + ROW_ACCESS_DELAY + COL_ACCESS_DELAY << " Column number " << col << " being fetched" << endl;
                    }

                    else if (row == Row_number)
                    {
                        required_clock = COL_ACCESS_DELAY;
                        cout << "Cycle " << cycle+ 1 << "-" << cycle + COL_ACCESS_DELAY << " Column number " << col << " being fetched" << endl;
                        curr_row = row;
                    }
                    else
                    {
                        required_clock = 2*ROW_ACCESS_DELAY + COL_ACCESS_DELAY;
                        cout << "Cycle " << cycle+1 << "-" << cycle + ROW_ACCESS_DELAY << " Row buffer " << "being copied to the DRAM" << endl; 
                        cout << "Cycle " << cycle +1 + ROW_ACCESS_DELAY << "-" << cycle + 2 * ROW_ACCESS_DELAY << " Row number " << row << " being copied to the Row buffer" << endl; 
                        cout << "Cycle " << cycle + 2*ROW_ACCESS_DELAY + 1 << "-" << cycle + 2*ROW_ACCESS_DELAY + COL_ACCESS_DELAY << " Column number " << col << " being fetched" << endl;
                        curr_row = row;
                    }
                }
                //time to execute
                else if (dram_request[PC] && dram_execute)
                {
                    //dram request is already raised
                    tuple<string, uint32_t, uint32_t> tup = RequestManager[PC];
                    performSw(get<1>(tup), get<2>(tup), i);
                }
                //dram request is raised but not executed yet
                else
                {
                    
                    DRAM_busy = true;
                    if (Row_number == -1)
                    {
                        curr_row = row;
                        required_clock = COL_ACCESS_DELAY + ROW_ACCESS_DELAY;
                        cout << "Cycle " << cycle << "-" << cycle-1 + ROW_ACCESS_DELAY << " Row number " << row << " being copied to the Row buffer" << endl;
                        cout << "Cycle " << cycle + ROW_ACCESS_DELAY << "-" << cycle -1 + ROW_ACCESS_DELAY + COL_ACCESS_DELAY << " Column number " << col << " being fetched" << endl;
                    }

                    else if (row == Row_number)
                    {
                        required_clock = COL_ACCESS_DELAY;
                        cout << "Cycle " << cycle  << "-" << cycle-1+COL_ACCESS_DELAY << " Column number " << col << " being fetched" << endl;
                        curr_row = row;
                    }
                    else
                    {
                        required_clock = 2*ROW_ACCESS_DELAY + COL_ACCESS_DELAY;
                        curr_row = row;
                        cout << "Cycle " << cycle << "-" << cycle -1 + ROW_ACCESS_DELAY << " Row buffer " << "being copied to the DRAM" << endl; 
                        cout << "Cycle " << cycle+ ROW_ACCESS_DELAY << "-" << cycle-1 + 2 * ROW_ACCESS_DELAY << " Row number " << row << " being copied to the Row buffer" << endl; 
                        cout << "Cycle " << cycle + 2*ROW_ACCESS_DELAY << "-" << cycle -1 + 2*ROW_ACCESS_DELAY + COL_ACCESS_DELAY<< " Column number " << col << " being fetched" << endl;
                    }
                }
            }
            else 
            {
                //raising dram request
                if (row == curr_row)
                {
                    if (instr_buffer.size() < 3)
                    {
                        instr_buffer.push(PC);
                    }
                }
                else
                {
                    if (!last_set)
                    {
                        last = PC;
                        last_set = true;
                    }
                }
                if (!dram_request[PC])
                {
                    dram_request[PC] = true;
                    cout << "Cycle " << cycle << " Core " << i << ": DRAM request raised for instruction " << PC << endl;
                    uint32_t val = RegisterValues[src];
                    RequestManager[PC] = make_tuple ("sw", val, curr_address);
                }
                
            }
            PC = PC + 1;
        }
        else
        {
            halt = 1;
        }
    }
}

void Core::performLw(uint32_t reg, uint32_t address, int i)
{
    if (!completed[PC])
    {
        uint32_t row = address/1024;
        uint32_t col = address - 1024*row;
        col = col/4;

        if (Row_number == -1)
        {
            Row_number = row;
            copy_n(DRAM[Row_number], 256, Row_buffer);
            RegisterValues[reg] = Row_buffer[col];
            dram_access += 1;
        }
        else
        {
            if (Row_number == row)
            {
                RegisterValues[reg] = Row_buffer[col];
            }
            else
            {
                Row_number = row;
                copy_n(DRAM[Row_number], 256, Row_buffer);
                RegisterValues[reg] = Row_buffer[col];
                dram_access += 1;
            }
        }
        total += 1;
        cout << "Cycle " << cycle << " Core " << i << ": Executed instruction " << PC << endl;
        completed[PC] = true;
    }
}

void Core::performSw(uint32_t val, uint32_t address, int i)
{
    if (!completed[PC])
    {
        uint32_t row = address/1024;
        uint32_t col = address - 1024*row;
        col = col/4;

        if (Row_number == -1)
        {
            Row_number = row;
            copy_n(DRAM[Row_number], 256, Row_buffer);
            Row_buffer[col] = val;
            dram_access += 1;
        }
        else
        {
            if (Row_number == row)
            {
                Row_buffer[col] = val;
            }
            else
            {
                Row_number = row;
                copy_n(DRAM[Row_number], 256, Row_buffer);
                Row_buffer[col] = val;
                dram_access += 1;
            }
        }
        total += 1;
        cout << "Cycle " << cycle << " Core " << i << ": Executed instruction " << PC << endl;
        completed[PC] = true;
    }
}

void Core::Execute(int i)
{
    
    if (halt == 0)
    {
        if (PC < Total_instructions)
        {
            while (PC < Total_instructions && completed[PC])
            {
                PC = PC + 1;
            }
            if (!completed[PC])
            {
                ExecuteInstruction(Memory[PC], i);
            }
        }
    }
    else
    {
        cout << "Cycle " << cycle << " Core " << i << " is on halt" << endl;
    }
}

void performBufferExecution(vector<Core> &cores, int num, int m, int n)
{
    cores[num].dram_execute = true;
    while (cycle < m && cores[num].instr_buffer.size() > 0)
    {
        cores[num].PC = cores[num].instr_buffer.front();
        cores[num].instr_buffer.pop();
        cores[num].ExecuteInstruction(cores[num].Memory[cores[num].PC], num);
        cycle = cycle + cores[num].COL_ACCESS_DELAY;
    }
    cores[num].dram_execute = false;
}

void performDramExecution(vector<Core> &cores, int num, int m, int n)
{
    int temp = 0;
    uint32_t pending = cores[num].PC;

    for (int i = 0; i < n; i++)
    {
        cores[i].Execute(i);
    }
    cycle = cycle + 1;
    
    while (cycle < m && temp < required_clock - 1)
    {
        for (int i = 0; i < n; i++)
        {
            if (i != num)
            {
                cores[i].Execute(i);
            }
            else
            {
                cores[i].Execute(i);
            }
        }
           
        cycle = cycle + 1;
        temp = temp + 1;
    }
    
    if (cycle < m)
    {
        uint32_t PC_prev = cores[num].PC;
        cores[num].PC = pending;
        
        for (int i = 0; i < n; i++)
        {
            if (i != num)
            {
                cores[i].Execute(i);
            }
            else
            {
                cores[i].dram_execute = true;
                cores[i].ExecuteInstruction(cores[i].Memory[cores[i].PC], i);
                cores[i].dram_execute = false;
            }
        }
        cycle = cycle + 1;
        cores[num].PC = PC_prev;
    }
}

void performExecution(vector<Core> &cores, int m, int n)
{
    bool busy = false;
    int num;

    for (int i = 0; i < n; i++)
    {
        uint32_t opcode = cores[i].Memory[cores[i].PC];
        string bin = cores[i].binary(opcode);
        string cmd = bin.substr(0,6);
        
        if (cmd == "100011" || cmd == "101011")
        {
            busy = true;
            num = i;
            break;
        }
    }

    cout << "Cycle " << cycle << "-" << cycle + MRM_cycles - 1 << ": MRM cycles" << endl;
    cycle = cycle + MRM_cycles;
    total_mrm += MRM_cycles;

    if (busy == true)
    {
        performDramExecution(cores, num, m , n);
        if (cycle < m)
        {
            if (cores[num].instr_buffer.size() > 0)
            {
                performBufferExecution(cores, num, m, n);
            }
            DRAM_busy = false;
            for (int i = 0; i < n; i++)
            {
                cores[i].conflict.clear();
                if (cores[i].last_set == true)
                {
                    cores[i].PC = cores[i].last;
                    cores[i].last_set = false;
                }
                cores[i].halt = 0;
            }
        }
    }

    else
    {
        for (int i = 0; i < n; i++)
        {
            cores[i].Execute(i);
        }
        cycle = cycle + 1;
    }
}

int main(int argc, char** argv) 
{
    cout << "enter the number of cores: " << endl;
    int n, m;
    cin >> n;
    cout << "enter the number of cycles: " << endl;
    cin >> m;

    vector<Core> cores;
    string infile;
    for (int i = 0; i < n; i++)
    {
        cin >> infile;
        cores.push_back(Core(infile));
        cores[i].Storing();
    }
    
    cycle = 0;
    while (cycle < m)
    {
        performExecution(cores, m, n);
    }
    cout << " " << endl;
    
    for (int i = 0; i < n; i++)
    {
        cout << "Core " << i << ": Total instructions executed = " << cores[i].total << endl;
        cout << "Core " << i >> ": Total DRAM acceses = " << cores[i].dram_access << endl;
        cout << " " << endl;
    }
    cout << "Total MRM cycles: " << total_mrm << endl;
    return 1;
}
