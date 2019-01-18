# Converter from Context Free Grammar to Chomsky Normal Form
#
# Luca Gilardi


# NOTES: this converter supposes to receive the correct inputs whenever they are asked, for example for the number of
# rules that have to be inserted and the very own rules.
# In particular, it does NOT check whether the grammar passed as an input is a Context Free Grammar or not,
# please keep this in mind.
# Finally, it is not optimized, for example sometimes it does not reuses the same non terminals when possible,
# for example if we have "A -> x" and "B -> x" it may use both A and B even if we may substitute one of them
# in the other rules of the grammar.


# Imports
from string import ascii_letters
import re
import copy

# -------------------------------------------------------------------------------------
# ------------------------- Functions definition --------------------------------------
# -------------------------------------------------------------------------------------


# Print grammar in nice format
def show_grammar(rules):
    for i in rules:
        for j in rules[i]:
            print('{} -> {}'.format(i, j))


# Check if string contains lowercase character(s)
def str_contains_low(s):
    for i in s:
        if i.islower():
            return True
    return False


# Check if list contains string(s) with lowercase character(s)
def list_contains_low(l):
    for i in l:
        if len(i) != 1:
            if str_contains_low(i) == True:
                return True
    return False


# Remove identical rules, such as A -> a and A -> a
def remove_duplicates(rules):
    for i in rules:
        for j in rules[i]:
            if list(rules[i]).count(j) > 1:
                rules[i].remove(j)
    return rules


# Find list of all terminals with the given set of grammar rules
def find_terminals(rules):
    temp = []
    for i in rules:
        for j in rules[i]:
            for k in j:
                if k.islower() and k not in temp:
                    temp.append(k)
    return temp


# Add one new rule for each terminal found with the function find_terminals, e.g. Z -> x
def add_terminal_rules(rules, list_terminals, let):
    for i in list_terminals:
        new_nt = let[-1]
        let.remove(new_nt)
        rules.setdefault(new_nt, []).append(i)
    return rules, let


# Remove all the terminals in the rules (except for the one added with add_terminal_rules)
# and substitute the corresponding non terminal rule
def substitute_terminal_rules(rules):
    temp = {}  # used for
    for i in rules:
        for j in rules[i]:
            if len(j) == 1 and j.islower():
                temp[j] = i  # NB: terminals are keys, non terminals are values
    for i in rules:
        if i not in list(temp.values()):
            for j in rules[i]:
                for h in j:
                    if h in list(temp.keys()):
                        new = copy.deepcopy(j)
                        new = new.replace(h, temp[h])
                        if j in rules[i]:
                            rules[i].remove(j)
                            rules.setdefault(i, []).append(new)
    return rules


# step 1 indicated in the slides
def step1(rules):
    for i in rules:
        while list_contains_low(rules[i]):
            rules = substitute_terminal_rules(rules)
    return rules


# For all "long rules" substitute the last two characters with a new one
def change_last_elements(rules):
    new_dict = copy.deepcopy(rules)
    temp = {}
    for i in rules:
        for j in rules[i]:
            if len(j) > 2 and j[-2:] not in list(temp.keys()):
                new_nt = let[-1]
                let.remove(new_nt)
                new_dict.setdefault(new_nt, []).append(j[-2:])
                temp[j[-2:]] = new_nt
    for i in new_dict:
        for j in new_dict[i]:
            if j[-2:] in list(temp.keys()) and i not in list(temp.values()):
                new = copy.deepcopy(j)
                new = new.replace(j[-2:], temp[j[-2:]])
                if j in new_dict[i]:
                    new_dict[i].remove(j)
                    new_dict.setdefault(i, []).append(new)
    return new_dict


# Find if a rule has more than 2 characters
def long_rule(rules):
    for i in rules:
        for j in rules[i]:
            if len(j) > 2:
                return True
    return False


# Step 2 indicated in the slides (it calls change_last_elements until there are no more long rules)
def step2(rules):
    while long_rule(rules):
        rules = change_last_elements(rules)
    return rules


# Step 3 indicated on the slide (just add the S0 symbol and link with S)
def step3(rules):
    if '/' in rules['S']:  # I chose S as starting symbol
        rules.setdefault('S0', []).append('/')
        rules['S0'].append('S')
        # rules['S'].remove('/')
    return rules


# Find if there are chain rules, i.e. A -> B and B -> C results in A -> C
def chain_rule_presence(rules, terminals):
    for i in rules:
        for j in rules[i]:
            if j in list(rules.keys()) and rules[j][0] not in terminals:
                return True
    return False


# Apply the chain rules
def apply_chain_rule(rules, terminals):
    new_dict = copy.deepcopy(rules)
    temp = {}
    for i in new_dict:
        for j in new_dict[i]:
            if j in list(new_dict.keys()):
                for k in new_dict[j]:
                    if k not in terminals:
                        new_dict[i].append(k)
                if rules[j][0] not in terminals:
                    new_dict[i].remove(j)
    return new_dict


# Short rule = A -> B
# It removes rules like A -> B and it adds A -> x, if B -> x
# This function relies on the fact that if there is such short rule at this point of the computation
# it can only be due to the fact that B (in the example above) is a rule such as B -> x, where x is a terminal.
def remove_short_rules(rules):
    for i in rules:
        for j in rules[i]:
            if len(j) == 1 and j[0].isupper():
                rules[i].append(rules[j][0])
                rules[i].remove(j)
    return rules


# Find if there are still short rules
def find_short_rule(rules):
    for i in rules:
        for j in rules[i]:
            if len(j) == 1 and j[0].isupper():
                return True
    return False


# Step 5 indicated in the slides; it calls apply_chain_rule as long as chain rules are present
def step5(rules, terminals):
    temp = {}
    while (chain_rule_presence(rules, terminals)):
        rules = apply_chain_rule(rules, terminals)
    for i in rules:
        c = list(set(rules[i]))
        for j in c:
            temp.setdefault(i, []).append(j)
    while find_short_rule(temp):
        temp = remove_short_rules(temp)
    return temp


# Find if there are empty rules (not considering S and eventually S0)
def empty_rule_presence(rules):
    for i in rules:
        if i not in (['S0']) and '/' in rules[i]:
            return True
    return False


# Core function of step 4: it applies the transformations indicated in the slides accordingly to the rigth case
def remove_empty_productions(rules):
    new_dict = copy.deepcopy(rules)
    temp = []
    for i in rules:
        if '/' in rules[i] and i not in (['S0']):
            temp.append(i)  # save in temp all the non terminals NT which contain a rule like NT -> /
    for x in temp:
        l_x = len(list(rules[x]))
        # if x contains only '/' remove x -> '/' and remove x from all the production rules
        if l_x == 1:
            for i in new_dict:
                if i != x:
                    for j in new_dict[i]:
                        if x in j:
                            if len(j) > 1:
                                new = j.replace(x, '')
                                new_dict[i].append(new)
                                new_dict[i].remove(j)
                            if len(j) == 1:
                                new_dict[i].append('/')
                                new_dict[i].remove(j)

        # if x ALSO contains '/' remove x -> '/' and add D -> '/' (if D -> x) or C -> y (if C -> xy or C -> yx)
        if l_x > 1:
            for i in new_dict:
                if i != x:
                    for j in new_dict[i]:
                        if x in j:
                            if len(j) > 1:
                                new = j.replace(x, '')
                                if new not in new_dict[i]:
                                    new_dict[i].append(new)
                                # new_dict[i].remove(j)
                            if len(j) == 1:
                                new_dict[i].append('/')
                                # new_dict[i].remove(j)
        new_dict[x].remove('/')
    return new_dict


# Final removal of empty rules (not considering S and eventually S0)
def remove_empty_rules(rules):
    temp = {}
    for i in rules:
        for j in rules[i]:
            if j != '/' or i in (['S0']):
                temp.setdefault(i, []).append(j)
    return temp


# Step 4 indicated in the slides;
def step4(rules):
    new = remove_empty_productions(rules)
    while empty_rule_presence(new):
        temp = copy.deepcopy(new)
        new = remove_empty_productions(new)
        if temp == new:
            break
    new = remove_empty_rules(new)
    new = remove_duplicates(new)
    return new


# Remove unreachable rules
def remove_unreachable(rules):
    new_dict = copy.deepcopy(rules)
    temp = []
    for i in rules:
        for j in rules[i]:
            for k in j:
                temp.append(k)
    for i in rules:
        if i not in temp and i not in (['S0']):
            del new_dict[i]
    return new_dict


# Main function: it applies all the transformations above
def convert(rules, let, terminals):
    print('Initial rules: ', rules)

    print('Terminals: ', terminals)

    rules, let = add_terminal_rules(rules, terminals, let)
    print('Rules after adding terminals: ', rules)

    rules = step1(rules)
    print('Rules after step #1: ', rules)

    rules = step2(rules)
    print('Rules after step #2: ', rules)

    rules = step3(rules)
    print('Rules after step #3: ', rules)

    rules = step4(rules)
    print('Rules after step #4:', rules)

    rules = step5(rules, terminals)
    print('Rules after step #5:', rules)

    rules = remove_unreachable(rules)
    print('Rules after removing unreachable rules:', rules)

    return rules

# -------------------------------------------------------------------------------------------------------------
# -------------------------------- MAIN BODY ------------------------------------------------------------------
# -------------------------------------------------------------------------------------------------------------

let = list(ascii_letters[:])  # letters pool (lowercase + uppercase characters)
let_low = let[:26]  # lowercase characters
let_up = let[26:]  # uppercase characters

rules = {}  # dictionary for the grammar rules

# Ask to the user how many rules he wants to add to the grammar (they should be at least 2)
while True:
    userInput = int(input('Give number of rules: '))
    try:
        # check if N >= 2
        N = int(userInput)
        if N < 2:
            print('N must be greater or equal to 2')
        else:
            break
    except ValueError:
        print("N must be an integer.")

print('Please insert the production rules of the grammar in the form A B (this stands for A -> B) '
      'or A BCD (for A -> BCD), \n'
      'in case of multiple non-terminals in the right hand side.\n'
      'Please use S as starting symbol and "/" to indicate the empty string epsilon.\n'
      'Please use non-terminals of only one character')

# Generate the grammar adding the rules given as an input
for i in range(N):
    # The user gives rules in the form "y x" insted of "y -> x"
    y, x = map(str, input('Rule #' + str(i + 1)).split())

    # Remove non terminals in the inserted rules from "letters pool"
    for l in y:
        if l in let:
            let.remove(l)
    for l in x:
        if l in let and l.isupper():
            let.remove(l)

    # Insert rule to dictionary
    rules.setdefault(y, []).append(x)

# terminals contained in the grammar rules
terminals = []
terminals = find_terminals(rules)

# find the Chomsky Normal Form of the given grammar
rules = convert(rules, let, terminals)

# Just print the CNF grammar in a classic format
print('\nThe corresponding Chomsky Normal Form of the given grammar is: \n')
show_grammar(rules)
