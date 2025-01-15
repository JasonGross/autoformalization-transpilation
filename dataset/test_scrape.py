from scrape import process_coq_file, build_module_tree, get_path_at_position
import json

# Test content from Imp.v
TEST_CONTENT = '''Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Module HypothesisNames.

(** A small notational aside. We could also write the definition of
    [aevalR] as follow, with explicit names for the hypotheses in each
    case: *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).

End HypothesisNames.'''

def test_module_tree():
    # Write test content to a temporary file
    with open('test_imp.v', 'w') as f:
        f.write(TEST_CONTENT)
    
    with open('test_imp.v', 'r') as f:
        coq_text = f.read()
    
    # Build and verify module tree
    tree = build_module_tree(coq_text)
    
    # Test full file processing
    result = process_coq_file('test_imp.v')
    
    print("\nModule Tree Structure:")
    def print_tree(node, level=0):
        print("  " * level + f"- {node.name} ({node.start_pos}, {node.end_pos})")
        for child in node.children:
            print_tree(child, level + 1)
    
    print_tree(tree)
    
    print("\nProcessed file results:")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    test_module_tree()
