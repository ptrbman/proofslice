void main() {
    int balance = 100;
    int transaction = 50;
    int fee = 2;

    int approved;
    int final_balance;

    if (transaction > balance) {
        approved = 0; 
        final_balance = balance;
    } else {
        approved = 1; 
        final_balance = balance - transaction - fee;
    }

    if (balance > transaction) {
        approved = approved;
    } else {
        final_balance = final_balance;
    }

    assert(final_balance == 48);  
}
