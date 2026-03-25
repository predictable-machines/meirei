/-
  Banking Reference — Meirei Translation

  Approximate translation of predictable-machines/predictable-code-java-reference,
  a vanilla Java banking application (Java 17+, no frameworks), into Meirei's
  imperative IR.

  Java source files → Meirei sections:
    TransactionType.java  → TransactionType enum
    Account.java          → Account struct + deposit/withdraw functions
    Transaction.java      → Transaction struct + factory functions
    Bank.java             → Bank struct + query functions (partial)
    Main.java             → Demo scenario as pure computation
-/

import Meirei.IR.Meirei.Index

open Meirei

namespace BankingReference

-- =============================================================================
-- TransactionType.java
-- =============================================================================

-- Java: public enum TransactionType { DEPOSIT, WITHDRAWAL, TRANSFER }
meirei_type enum TransactionType { Deposit(), Withdrawal(), Transfer() }

#check TransactionType
#check TransactionType.Deposit
#check TransactionType.Withdrawal
#check TransactionType.Transfer

def txTypeCode := [Meirei|
  def txTypeCode(t: TransactionType): Int {
    match t {
      case TransactionType.Deposit() { return 1; }
      case TransactionType.Withdrawal() { return 2; }
      case TransactionType.Transfer() { return 3; }
    }
  }
]

#guard txTypeCode TransactionType.Deposit == 1
#guard txTypeCode TransactionType.Withdrawal == 2
#guard txTypeCode TransactionType.Transfer == 3

-- =============================================================================
-- Account.java
-- =============================================================================

-- Java: class Account { private final String id; private int balance; }
meirei_type struct Account { id: String, balance: Int }

#check Account
#check Account.mk
#check @Account.id
#check @Account.balance

-- Java: public void deposit(int amount) { balance += amount; }
-- Pure: returns new Account instead of mutating
def accountDeposit := [Meirei|
  def accountDeposit(account: Account, amount: Int): Account {
    return Account.mk(account.id, account.balance + amount);
  }
]

#check accountDeposit
#guard accountDeposit (Account.mk "alice" 1000) 200 == Account.mk "alice" 1200

-- Java: public void withdraw(int amount) { ... balance -= amount; }
-- Preconditions (amount > 0, balance >= amount) assumed — no exceptions in Meirei
def accountWithdraw := [Meirei|
  def accountWithdraw(account: Account, amount: Int): Account {
    return Account.mk(account.id, account.balance - amount);
  }
]

#check accountWithdraw
#guard accountWithdraw (Account.mk "bob" 500) 100 == Account.mk "bob" 400

-- Java: public int getBalance() { return balance; }
def accountBalance := [Meirei|
  def accountBalance(account: Account): Int {
    return account.balance;
  }
]

#guard accountBalance (Account.mk "alice" 1000) == 1000

-- Java: public String getId() { return id; }
def accountId := [Meirei|
  def accountId(account: Account): String {
    return account.id;
  }
]

#guard accountId (Account.mk "alice" 1000) == "alice"

-- String literals used directly in Meirei function bodies
def defaultAccount := [Meirei|
  def defaultAccount(balance: Int): Account {
    return Account.mk("default", balance);
  }
]

#guard defaultAccount 0 == Account.mk "default" 0
#guard defaultAccount 1000 == Account.mk "default" 1000

-- String literals in various Meirei expression positions

-- In return position (standalone)
def stringReturn := [Meirei|
  def stringReturn(): String {
    return "hello";
  }
]

#guard stringReturn == "hello"

-- In var initializer + assignment inside a loop
def stringInAssign := [Meirei|
  def stringInAssign(xs: [Int]): String {
    var name: String = "initial";
    for x in xs {
      name = "updated";
    }
    return name;
  }
]

#guard stringInAssign [1] == "updated"
#guard stringInAssign [] == "initial"

-- In binary comparison (if-else, not if-return which needs a loop)
def stringInCondition := [Meirei|
  def stringInCondition(name: String): Int {
    if (name == "alice") {
      return 1;
    } else {
      return 0;
    }
  }
]

#guard stringInCondition "alice" == 1
#guard stringInCondition "bob" == 0

-- =============================================================================
-- Transaction.java
-- =============================================================================

-- Java uses null for absent account IDs → Meirei uses Option (String?)
-- Timestamp (java.time.Instant) omitted — no time type in Meirei
meirei_type struct Transaction {
  txType: TransactionType,
  fromId: String?,
  toId: String?,
  amount: Int
}

#check Transaction
#check Transaction.mk

-- Java: new Transaction(TransactionType.DEPOSIT, null, accountId, amount)
def makeDepositTx := [Meirei|
  def makeDepositTx(toId: String, amount: Int): Transaction {
    return Transaction.mk(TransactionType.Deposit(), none, some(toId), amount);
  }
]

-- Java: new Transaction(TransactionType.WITHDRAWAL, accountId, null, amount)
def makeWithdrawalTx := [Meirei|
  def makeWithdrawalTx(fromId: String, amount: Int): Transaction {
    return Transaction.mk(TransactionType.Withdrawal(), some(fromId), none, amount);
  }
]

-- Java: new Transaction(TransactionType.TRANSFER, fromId, toId, amount)
def makeTransferTx := [Meirei|
  def makeTransferTx(fromId: String, toId: String, amount: Int): Transaction {
    return Transaction.mk(TransactionType.Transfer(), some(fromId), some(toId), amount);
  }
]

-- Java: public int getAmount() { return amount; }
def txAmount := [Meirei|
  def txAmount(tx: Transaction): Int {
    return tx.amount;
  }
]

#guard txAmount (makeTransferTx "alice" "bob" 300) == 300

-- =============================================================================
-- Bank.java (partial — stateful collection mutations cannot be expressed)
-- =============================================================================

meirei_type struct Bank {
  accounts: [Account],
  transactions: [Transaction]
}

-- Java: private Account getAccount(String id) { accounts.get(id); ... }
-- Returns balance for account with given ID, 0 if not found.
-- Uses accountId/accountBalance helpers because field access on loop
-- variables is not yet supported in Meirei's loop elaboration.
def findAccountBalance := [Meirei|
  def findAccountBalance(accounts: [Account], id: String): Int {
    for a in accounts {
      if (accountId(a) == id) {
        return accountBalance(a);
      }
    }
    return 0;
  }
]

#guard findAccountBalance [Account.mk "alice" 1000, Account.mk "bob" 500] "alice" == 1000
#guard findAccountBalance [Account.mk "alice" 1000, Account.mk "bob" 500] "bob" == 500
#guard findAccountBalance [Account.mk "alice" 1000, Account.mk "bob" 500] "eve" == 0

-- Compute total balance across all accounts.
-- Parentheses around the function call are needed for parser precedence.
def totalBalance := [Meirei|
  def totalBalance(accounts: [Account]): Int {
    var total: Int = 0;
    for a in accounts {
      total = total + (accountBalance(a));
    }
    return total;
  }
]

#guard totalBalance [Account.mk "alice" 1000, Account.mk "bob" 500] == 1500
#guard totalBalance [] == 0

-- Count entries in the transaction log
def countTransactions := [Meirei|
  def countTransactions(txns: [Transaction]): Int {
    var count: Int = 0;
    for t in txns {
      count = count + 1;
    }
    return count;
  }
]

-- =============================================================================
-- Main.java → Demo Scenario
-- =============================================================================

/-
  Java Main.main() does:
    Bank bank = new Bank();
    bank.createAccount("alice", 1000);
    bank.createAccount("bob",   500);
    bank.deposit("alice", 200);          → alice = 1200
    bank.withdraw("bob", 100);           → bob   = 400
    bank.transfer("alice", "bob", 300);  → alice = 900, bob = 700
    bank.printSummary();
-/

-- Alice: initial=1000, deposit 200, transfer out 300 → 900
def aliceFinalBalance := [Meirei|
  def aliceFinalBalance(initial: Int, depositAmt: Int, transferOut: Int): Int {
    return initial + depositAmt - transferOut;
  }
]

-- Bob: initial=500, withdraw 100, transfer in 300 → 700
-- Parens needed: Meirei binary ops are right-associative at the same precedence
def bobFinalBalance := [Meirei|
  def bobFinalBalance(initial: Int, withdrawAmt: Int, transferIn: Int): Int {
    return (initial - withdrawAmt) + transferIn;
  }
]

#guard aliceFinalBalance 1000 200 300 == 900
#guard bobFinalBalance 500 100 300 == 700

-- End-to-end demo using the Account struct operations, mirroring Main.java
#guard (
  let alice := Account.mk "alice" 1000
  let bob := Account.mk "bob" 500
  let alice := accountDeposit alice 200
  let bob := accountWithdraw bob 100
  let alice := accountWithdraw alice 300
  let bob := accountDeposit bob 300
  (alice.balance, bob.balance) == (900, 700)
)

end BankingReference

/-
  =============================================================================
  Gaps: Java features requiring new Meirei capabilities
  =============================================================================

  1. EXCEPTIONS / VALIDATION — Java's Account.deposit and withdraw throw
     IllegalArgumentException on invalid inputs (non-positive amounts,
     insufficient funds). Meirei functions assume preconditions hold.
     A Result type or error-return mechanism would capture this.

  2. MUTABLE COLLECTIONS — Bank.java maintains a HashMap<String, Account>
     and ArrayList<Transaction> that grow over time. Meirei cannot append
     to, replace in, or construct lists. List primitives (cons, append,
     map, filter) would enable full Bank.createAccount / Bank.deposit /
     Bank.withdraw / Bank.transfer translation.

  3. TIMESTAMP — Transaction.timestamp uses java.time.Instant. No clock
     or time type exists in Meirei.
-/
