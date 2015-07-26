///\file poker.cpp
///\brief Rigorously-specified poker hands comparison
///
///Implements the poker game and provides formal specifications of it's rules as described in
///http://en.wikipedia.org/wiki/List_of_poker_hands#General_rules and http://en.wikipedia.org/wiki/List_of_poker_hands#Standard_ranking

/**\mainpage Poker Project

\author Mauro Baluda (id: 67153101)\n mauro@bglug.it

\section intro_sec 1 Introduction

This project is meant as an exercise in formal specification of software systems.\n
My goal was to create a system that could compare two poker hands and determine the winner following the rules that can be found in\n
http://en.wikipedia.org/wiki/List_of_poker_hands#General_rules and http://en.wikipedia.org/wiki/List_of_poker_hands#Standard_ranking

The code presented includes the specification, the documentation and the implementation of the system.\n

\section spec_sec 2 The specification
To determine which is the higher hand in a match I developed a "signature based method".\n
Is possible to determine a unique signature for all the hands of the same category simply counting the frequencies of all the distinct ranks that take part in the hand and than sort them in descending order obtaining:\n
\code
Straight flush -> 11111
Four of a kind -> 41
Full House -> 32
Flush -> 11111
Straight -> 11111
Three of A Kind -> 311
Two Pair -> 221
One pair -> 2111
High Card -> 11111
\endcode
Straight flush, Flush, Straight, High Card obtain the same 11111 signature but they can anyway be easily classified looking directly at their cards.\n
Keeping also track of the ranks that generated those signature makes it very easy to determine the winner between two hands of the same category looking at the leftmost different rank as in the following example:
\code
8C 8D 6S 4D 5S -> 21111
8S 7D 8H 4S 5D -> 21111
\endcode
both are "One Pair" so we need to look at the ranks:
\code
2-8 1-6 1-5 1-4 (freq-rank)
2-8 1-7 1-5 1-4 (freq-rank)
\endcode
the first different rank is in second position: 6 vs 7 so the second hand wins.\n
this strategy works for all of the different categories.

\section special_case 2.1 Special Case
A special case that needs to be addressed is the "low A in Straights" like 5432A, the case is anyway easily recognizable.

\section ambiguities 2.2 Ambiguities
When is not possible to determine which hand wins the match (all the cards have the same rank but different suit), the specification says that the match result is tie.\n
It would be possible to rise the computer chances to win on the long run solving this kind of ambiguities in his favor.

\section implementation_sec 3 Implementation
The specification is written in natural/mathematical language and some times in an OCL-like sintax.\n
The code is written in c++ using assertions heavily to verify the specifications at runtime thus obtaining a complete Design by Contract programming environment.\n
All the methods of the program verify their pre and post conditions (unless they are just a duplication of the function itself), all the public methods assert the Class Invariant at begin and end. The constructors verify the Class Invariant just before returning the control.

\subsection using 3.1 Using the program
The makefile provided is for linux systems but a win32 binary file is included (poker.exe).\n
The program can be tested from the command line passing as parameters one or two poker hands using the following sintax:
\code
Ranks: 2 3 4 5 6 7 8 9 X J Q K A
Suits: S C D H

example: ./poker XC 2H 3H 4D AS
example: ./poker 8C 7D 6S 4D 5S   7S 2S 5D 8S 6C
\endcode
The system will output the Hand classification and who is the winner.

\section documentation_sec 4 Documentation
The project and the code documentation was written using doxygen [http://www.stack.nl/~dimitri/doxygen/] a multi-language documentation system.

To generate the documentation you need to use the command 'make doc'.
*/

// includes
#include <utility>
#include <vector>
#include <algorithm>
#include <cassert>
#include <functional>
#include <iostream>

///\brief Holds the Card value, implements some useful operations
///\invariant 13 possible values for rank: \f$ 0 \leq rank \leq 12 \f$
///\code
///context PlayCard
///    inv rankRange: 0<=rank<=12
///\endcode
///\invariant 3 possible values for suit: \f$ 0 \leq rank \leq 3 \f$
///\code
///context PlayCard
///    inv suitRange: 0<=suit<=3
///\endcode
class PlayCard {
private:
    ///\brief Asserts the Class Invariant
    ///
    ///Used at the beginning and end of every public methods to verify that the Invariant holds
    void ClassInv() {
        assert(rank>=0);
        assert(rank<=12);
        assert(suit>=0);
        assert(suit<=3);
    }

public:
    ///\brief Holds the rank of the card
    int rank;
    ///\brief Holds the suit of the card
    int suit;

    ///\brief The default Constructor
    ///
    ///Makes the Class Invariant hold
    ///\post \f$ rank=0 \wedge suit=0 \f$
    ///\code
    ///context PlayCard::PlayCard(): void
    ///    post defConstr: rank=0 && suit=0
    ///\endcode
    PlayCard() {
        rank=0;
        suit=0;

        //check postcondition
        assert(rank==0);
        assert(suit==0);
        ClassInv();//Invariant holds
    }

    ///\brief The main Constructor
    ///
    ///Initialize the Class with parameters and makes the Class Invariant hold
    ///\pre \f$ 0 \leq r \leq 12 \wedge 0 \leq s \leq 3 \f$
    ///\code
    ///context PlayCard::PlayCard(int r, int s): void
    ///    pre mainConstr: 0<=rank<=12 && 0<=suit<=3
    ///\endcode
    ///\post \f$ rank=r \wedge suit=s \f$
    ///\code
    ///context PlayCard::PlayCard(int r, int s): void
    ///    post mainConstr: rank=r && suit=s
    ///\endcode
    ///@param[in] r: card rank \n
    ///@param[in] s: card suit \n
    PlayCard(int r, int s) {
        //check preconditions
        assert(r>=0);
        assert(r<=12);
        assert(s>=0);
        assert(s<=3);

        rank=r;
        suit=s;

        //check postcondition
        assert(rank==r);
        assert(suit==s);
        ClassInv();//Invariant holds
    }

    ///\brief Compares 2 card's rank (pure function)
    ///\post \f$ rank=other.rank \f$
    ///\code
    ///context PlayCard::equals(PlayCard: other): boolean
    ///    post equal: rank=other.rank
    ///\endcode
    bool sameRank(PlayCard other) {
        ClassInv();//Invariant holds

        bool result=(rank==other.rank);

        //check postcondition
        assert(result==(rank==other.rank));
        ClassInv();//Invariant holds
        return result;
    }

    ///\brief Compares 2 card's suit (pure function)
    ///\post \f$ suit=other.suit \f$
    ///\code
    ///context PlayCard::equals(PlayCard: other): boolean
    ///    post equal: suit==other.suit
    ///\endcode
    bool sameSuit(PlayCard other) {
        ClassInv();//Invariant holds

        bool result=(suit==other.suit);

        assert(result==(suit==other.suit));//post
        ClassInv();//Invariant holds
        return result;
    }

    ///\brief Compares 2 cards fo equality (pure function)
    ///\post \f$ rank=other.rank \wedge suit=other.suit \f$
    ///\code
    ///context PlayCard::equals(PlayCard: other): boolean
    ///    post equal: rank==other.rank && suit==other.suit
    ///\endcode
    bool equals(PlayCard other) {
        ClassInv();//Invariant holds

        bool result=(sameSuit(other)&&sameRank(other));

        assert(result==(rank==other.rank && suit==other.suit));//post
        ClassInv();//Invariant holds
        return result;
    }

    ///\brief Print a card value (pure function)
    ///
    ///Prints a card on standard output in readable format
    void print() {
        ClassInv();//Invariant holds

        char* r="23456789XJQKA";
        char* s="SCDH";
        std::cout<<r[rank]<<s[suit]<<" ";

        ClassInv();//Invariant holds
    }
};

///\brief Holds the Poker Hand and implements the poker rules
///\invariant No duplicated cards in the hand: \f$ \forall c1, c2 \in PlayCard, c1 \neq c2 \f$
///\code
///context PokerHand
///    inv nonDuplicateCard: self.cards -> forall(c1:PlayCard, c2:PlayCard | c1!=c2 -> !c1.equals(c2))
///\endcode
///\invariant cards are exactly 5
///\code
///context PokerHand
///    inv fiveCards: cards.size()=5
///\endcode
///\invariant Possible values for category: \f$ 0 \leq category \leq 8 \f$
///\code
///context PokerHand
///    inv categoryRange: 0<=category<=8
///\endcode
///\invariant The cards are sorted descending: \f$ (\forall {1 \leq i \leq 4} , cards_{i-1} \geq cards_i \wedge cards \neq A5432) \vee cards=5432A \f$
///\code
///context PokerHand
///    inv sorted: cardsAreSorted()
///\endcode
///\invariant Correct signature: sigfreq contains the frequencies of the different ranks in cards in descending order, sigrank contains the corrispondent rank
///\code
///context PokerHand
///    inv sorted: correctSignature()
///\endcode
///\invariant The hand is in the right category
///\code
///context PokerHand
///    inv rightCategory: if isStraightFlush() result=StraightFlush
///                       else if isFourOfAKind() result=isFourOfAKind
///                       else if isFullHouse() result=FullHouse
///                       else if isFlush() result=Flush
///                       else if isStraight() result=Straight
///                       else if isThreeOfAKind() result=ThreeOfAKind
///                       else if isTwoPair() result=TwoPair
///                       else if isOnePair() result=OnePair
///                       else result=HighCard
///\endcode
class PokerHand {
private:
    ///\brief Verify that the Class Invariant holds
    void ClassInv() {
        //no duplicate cards
        for (unsigned int i=0; i<cards.size(); i++)
            for (unsigned int j=i; j<cards.size(); j++)
                assert(!(i!=j && cards[i].equals(cards[j])));
        //number of cards
        assert(cards.size()==5);
        //category ranges
        assert(category>=0);
        assert(category<=8);
        //cards are sorted
        assert(cardsAreSorted());
        //signature is correct
        assert(correctSignature());
        //right category
        assert(isStraightFlush()||category!=8);
        assert(isFourOfAKind()||category!=7);
        assert(isFullHouse()||category!=6);
        assert(isFlush()||category!=5);
        assert(isStraight()||category!=4);
        assert(isThreeOfAKind()||category!=3);
        assert(isTwoPair()||category!=2);
        assert(isOnePair()||category!=1);
        assert(category==0 || isStraightFlush()||isFourOfAKind()||isFullHouse()||isFlush()||isStraight()||isThreeOfAKind()||isTwoPair()||isOnePair());
    }

    ///\brief check if the cards ar sorted (pure function)
    ///\post TRUE if the cards are sorted descending: \f$ result=(\forall {1 \leq i \leq 4} , cards_{i-1} \geq cards_i \wedge cards \neq A5432) \vee cards=5432A \f$
    ///\code
    ///context PokerHand::cardsAreSorted(): bool
    ///    post sorted: result = cards==5432A OR (forall 1<=i<=4, cards[i-1]<=cards[i] AND cards!=A5432 THAN result=true)
    ///\endcode
    bool cardsAreSorted() {
        //sorted descending
        bool sorted=true;
        for (unsigned int i=1; i<cards.size(); i++)
            sorted&=cards[i-1].rank>=cards[i].rank;
        //accept 5432A
        sorted|=(cards[0].rank==3 && cards[1].rank==2 &&  cards[2].rank==1 && cards[3].rank==0 && cards[4].rank==12);
        //refuse A5432
        sorted&=!(cards[0].rank==12 && cards[1].rank==3 &&  cards[2].rank==2 && cards[3].rank==1 && cards[4].rank==0);
        return sorted;
    }

    ///\brief sort the cards
    ///\post The cards are sorted descending: \f$ (\forall {1 \leq i \leq 4} , cards_{i-1} \geq cards_i \wedge cards \neq A5432) \vee cards=5432A \f$
    ///\code
    ///context PokerHand::sort(): void
    ///    post sorted: cardsAreSorted()=TRUE
    ///\endcode
    void sort() {
        //sort descending
        for (std::vector<PlayCard>::iterator It1=cards.begin(); It1!=cards.end(); It1++)
            for (std::vector<PlayCard>::iterator It2=It1; It2!=cards.end(); It2++)
                if (It2->rank > It1->rank) { //unsorted
                    int tmpr=It2->rank;
                    It2->rank=It1->rank;
                    It1->rank=tmpr;

                    int tmps=It2->suit;
                    It2->suit=It1->suit;
                    It1->suit=tmps;
                }

        //transform A5432 in 5432A
        if (cards[0].rank==12 && cards[1].rank==3 &&  cards[2].rank==2 && cards[3].rank==1 && cards[4].rank==0) {
            cards.push_back(PlayCard(cards[0].rank,cards[0].suit));
            cards.erase(cards.begin());
        }

        assert(cardsAreSorted());//postcondition holds
    }

    ///\brief check if the signature oh the Hand is correct (pure function)
    ///\post \f$ result=TRUE \Leftrightarrow \f$
    ///\post sigfreq holds the frequencies of the different ranks in cards:
    ///\post \f$ \forall {0 \leq i \leq card.countunique()}, sigfreq_i=cards.count(rank=sigrank_i) \wedge \f$
    ///\post sigfreq is ordered descending:
    ///\post \f$ \forall {1 \leq i \leq sigfreq.size()} , sigfreq_{i-1} \geq sigfreq_i \wedge \f$
    ///\post if two freq are the same, sigrank is ordered by rank descending:
    ///\post \f$ \forall {1 \leq i \leq sigfreq.size()} (sigfreq_{i-1} = sigfreq_i \Rightarrow sigrank_{i-1} > sigrank_i) \f$
    bool correctSignature() {
        bool correct=true;
        //post1

        //post2-3
        for (unsigned int i=0; i<sigfreq.size(); i++)
            for (unsigned int j=i+1; j<sigfreq.size(); j++) {
                correct&=(sigfreq[i]>=sigfreq[j]);
                if (sigfreq[i]==sigfreq[j]) correct&=(sigrank[i]>sigrank[j]);
            }

        return correct;
    }

    ///\brief calculates the signature
    ///\post correctSignature()=TRUE
    ///\code
    ///context PokerHand::sort(): void
    ///    post sorted: correctSignature()=TRUE
    ///\endcode
    void calcSignature() {
        //copy cards in sigrank
        for (unsigned int i=0; i<cards.size(); i++)
            sigrank.push_back(cards[i].rank);

        //delete duplicates in sigrank
        sigrank.erase(std::unique(sigrank.begin(), sigrank.end() ), sigrank.end() );

        for (unsigned int i=0; i<sigrank.size(); i++)
            sigfreq.push_back(0);
        //compile frequencies
        for (unsigned int i=0; i<cards.size(); i++)
            for (unsigned int j=0; j<sigrank.size(); j++)
                if (cards[i].rank==sigrank[j])
                    sigfreq[j]++;

        //sort sigfreq and sigranc according to sigfreq descending
        //for equal freq, sort with descending ranks
        for (unsigned int i=0; i<sigfreq.size(); i++) {
            for (unsigned int j=i; j<sigfreq.size(); j++) {
                if ((sigfreq[i]<sigfreq[j])||((sigfreq[i]==sigfreq[j])&&(sigrank[i]<sigrank[j]))) {
                    int tmp=sigfreq[i];
                    sigfreq[i]=sigfreq[j];
                    sigfreq[j]=tmp;

                    tmp=sigrank[i];
                    sigrank[i]=sigrank[j];
                    sigrank[j]=tmp;
                }
            }
        }

        assert(correctSignature());//check postconditions
    }

    ///\brief The hand is a Straight Flush? (pure function)
    ///\pre correct Signature
    ///\code
    ///context PokerHand::isStraightFlush(): bool
    ///    pre signature: correctSignature()=TRUE
    ///\endcode
    ///\post is Straight and is Flush
    ///\code
    ///context PokerHand::isStraightFlush(): bool
    ///    post straightflush: result=isStraight() AND isFlush()
    ///\endcode
    bool isStraightFlush() {
        assert(correctSignature());//check preconditions

        return (isStraight() && isFlush());
    };

    ///\brief The hand is Four of a Kind? (pure function)
    ///\pre correct Signature
    ///\code
    ///context PokerHand::isFourOfAKind(): bool
    ///    pre signature: correctSignature()=TRUE
    ///\endcode
    ///\post sigfreq=[4,1]
    ///\code
    ///context PokerHand::isFourOfAKind(): bool
    ///    post isfourofakind: result=sigfreq[0]==4 AND sigfreq[1]==1 and sigfreq.size()=2
    ///\endcode
    bool isFourOfAKind() {
        assert(correctSignature());//check preconditions

        if (sigfreq.size()==2 && sigfreq[0]==4 && sigfreq[1]==1)
            return true;
        return false;
    };

    ///\brief The hand is Full House? (pure function)
    ///\pre correct Signature
    ///\code
    ///context pokerHand::isFullHouse(): bool
    ///    pre signature: correctSignature()=TRUE
    ///\endcode
    ///\post sigfreq=[4,1]
    ///\code
    ///context pokerHand::isFullHouse(): bool
    ///    post isfullhouse: result=sigfreq[0]==3 AND sigfreq[1]==2 and sigfreq.size()=2
    ///\endcode
    bool isFullHouse() {
        assert(correctSignature());//check preconditions

        if (sigfreq.size()==2 && sigfreq[0]==3 && sigfreq[1]==2)
            return true;
        return false;
    };

    ///\brief The hand is Flush (pure function)
    ///\post same suit: \f$ result=TRUE \Leftrightarrow \forall {1 \leq i \leq cards.size()} , cards_{i}.suit = cards_0.suit \f$
    bool isFlush() {
        bool result=true;
        for (unsigned int i=0; i<cards.size(); i++)
            result&=(cards[i].suit==cards[0].suit);

        return result;
    };

    ///\brief The hand is Straight (pure function)
    ///\pre sorted cards
    ///\code
    ///context pokerHand::isStraight(): bool
    ///    pre isstraight: cardsAreSorted()
    ///\endcode
    ///\post isstraight: \f$ result=TRUE \Leftrightarrow \f$
    ///\post \f$ \forall {1 \leq i \leq cards.size()} , cards_{i}.suit+1 = cards_{i-1}.suit \vee cards=5432A \f$
    bool isStraight() {
        assert(cardsAreSorted());//check preconditions

        bool result=true;
        for (unsigned int i=1;i<cards.size();i++)
            result&=(cards[i].rank+1==cards[i-1].rank);

        //special case (low A)
        if (cards[0].rank==3 && cards[1].rank==2 &&  cards[2].rank==1 && cards[3].rank==0 && cards[4].rank==12)
            result=true;

        return result;
    };

    ///\brief The hand is Three of A Kind? (pure function)
    ///\pre correct Signature
    ///\code
    ///context pokerHand::isThreeOfAKind(): bool
    ///    pre signature: correctSignature()=TRUE
    ///\endcode
    ///\post sigfreq=[3,1,1]
    ///\code
    ///context pokerHand::isThreeOfAKind(): bool
    ///    post isthreeofakind: result=sigfreq[0]==3 AND sigfreq[1]==1 AND sigfreq[2]==1 AND sigfreq.size()=3
    ///\endcode
    bool isThreeOfAKind() {
        assert(correctSignature());//check preconditions

        if (sigfreq.size()==3 && sigfreq[0]==3 && sigfreq[1]==1 && sigfreq[2]==1)
            return true;
        return false;
    };

    ///\brief The hand is Two Pair? (pure function)
    ///\pre correct Signature
    ///\code
    ///context pokerHand::isTwoPair(): bool
    ///    pre signature: correctSignature()=TRUE
    ///\endcode
    ///\post sigfreq=[2,2,1]
    ///\code
    ///context pokerHand::isTwoPair(): bool
    ///    post istwopair: result=sigfreq[0]==2 AND sigfreq[1]==2 AND sigfreq[1]==1 AND sigfreq.size()=3
    ///\endcode
    bool isTwoPair() {
        assert(correctSignature());//check preconditions

        if (sigfreq.size()==3 && sigfreq[0]==2 && sigfreq[1]==2 && sigfreq[2]==1)
            return true;
        return false;
    };

    ///\brief The hand is One Pair? (pure function)
    ///\pre correct Signature
    ///\code
    ///context pokerHand::isOnePair(): bool
    ///    pre signature: correctSignature()=TRUE
    ///\endcode
    ///\post sigfreq=[2,1,1,1]
    ///\code
    ///context pokerHand::isOnePair(): bool
    ///    post isonepair: result=sigfreq[0]==2 AND sigfreq[1]==1 AND sigfreq[2]==1 AND sigfreq[3]==1 AND sigfreq.size()=4
    ///\endcode
    bool isOnePair() {
        assert(correctSignature());//check preconditions

        if (sigfreq.size()==4 && sigfreq[0]==2 && sigfreq[1]==1 && sigfreq[2]==1 && sigfreq[3]==1)
            return true;
        return false;
    };

    ///\brief Best hand inside the same category (pure function)
    ///\pre correct Signature
    ///\code
    ///context pokerHand::betterCards(): bool
    ///    pre signature: correctSignature()=TRUE
    ///\endcode
    ///\post Best straight: \f$ (category=8 \vee category=4) \Rightarrow \f$
    ///\post \f$ (cards[0].rank = other.cards[0] \Rightarrow result=0) \vee \f$
    ///\post \f$ (cards[0].rank > other.cards[0] \Rightarrow result=1) \vee \f$
    ///\post \f$ (cards[0].rank < other.cards[0] \Rightarrow result=2) \f$
    ///\post Best non straight: \f$ (category \neq 8 \wedge category \neq 4) \Rightarrow \f$
    ///\post \f$ imin=min(i) \mid sigrank[i] \neq other.sigrank[i] \f$
    ///\post \f$ \neg \exists imin \Rightarrow result=0 \f$
    ///\post \f$ sigrank[imin] > other.sigrank[imin] \Rightarrow result=1 \f$
    ///\post \f$ sigrank[imin] < other.sigrank[imin] \Rightarrow result=2 \f$
    ///\post the first different rank in sigrank decides all
    int betterCards(PokerHand other) {
        assert(correctSignature());//check preconditions

        if (category==8 || category==4) { //straights
            if (cards[0].rank==other.cards[0].rank) return 0;
            else if (cards[0].rank>other.cards[0].rank) return 1;
            else return 2;
        } else {
            for (unsigned int i=0;i<sigrank.size();i++) {
                if (sigrank[i]>other.sigrank[i]) return 1;
                else if (sigrank[i]<other.sigrank[i]) return 2;
            }
            return 0;
        }
        return true;
    }

public:
    ///the cards in the hand
    std::vector<PlayCard> cards;

    ///the "signature" of the hand
    std::vector<int> sigfreq;
    std::vector<int> sigrank;

    ///the category of the hand
    int category;

    ///\brief Inizialize the Hand with parameters and finds out it's category
    ///
    ///makes the Class invariant hold
    ///@param[in] r1 r2 r3 r4 r5 : card ranks \n
    ///@param[in] s1 s2 s3 s4 s5 : card suits \n
    ///\pre \f$ \forall i, 0 \leq r_i \leq 12 \wedge 0 \leq s_i \leq 3 \f$
    ///\code
    ///context PlayCard::PlayCard(int r, int s): void
    ///    pre mainConstr: 0<=rank<=12 && 0<=suit<=3
    ///\endcode
    PokerHand(int r1, int s1, int r2, int s2, int r3, int s3, int r4, int s4, int r5, int s5) {
        cards.push_back(PlayCard(r1,s1));
        cards.push_back(PlayCard(r2,s2));
        cards.push_back(PlayCard(r3,s3));
        cards.push_back(PlayCard(r4,s4));
        cards.push_back(PlayCard(r5,s5));
        //sort the cards
        sort();
        //calculating the signature
        calcSignature();
        //find the right category
        if (isStraightFlush()) category=8;
        else if (isFourOfAKind()) category=7;
        else if (isFullHouse()) category=6;
        else if (isFlush()) category=5;
        else if (isStraight()) category=4;
        else if (isThreeOfAKind()) category=3;
        else if (isTwoPair()) category=2;
        else if (isOnePair()) category=1;
        else category=0;
        ClassInv();//Invariant holds
    }

    ///\brief returns the hand category (pure function)
    ///\post result=category
    int getCategory() {
        ClassInv();//Invariant holds
        return category;
        ClassInv();//Invariant holds
    }

    ///\brief Print a hand's cards values and the category (pure function)
    void print() {
        ClassInv();//Invariant holds

        char* c[9];
        c[0]="HighCards";
        c[1]="OnePair";
        c[2]="TwoPair";
        c[3]="ThreeOfAKind";
        c[4]="Straight";
        c[5]="Flush";
        c[6]="FullHouse";
        c[7]="FourOfAKind";
        c[8]="StraightFlush";

        for (unsigned int i=0; i<cards.size(); i++)
            cards[i].print();
        std::cout<<": "<<c[category]<<std::endl;

        ClassInv();//Invariant holds
    }

    ///\brief Returns TRUE if the current hand wins over the parameter one (pure function)
    ///\pre no duplicates in 2 hands: \f$ \forall i,j | 0 < i,j < cards.size(), cards[i] \neq other.cards[j] \f$
    ///\post \f$ category > other.category \Rightarrow result=1 \f$
    ///\post \f$ category < other.category \Rightarrow result=2 \f$
    ///\post \f$ category = other.category \Rightarrow result=batterCards(other) \f$
    int wins(PokerHand other) {
        ClassInv();//Invariant holds
        //no duplicated cards in the 2 hands
        for (unsigned int i=0; i<cards.size(); i++)
            for (unsigned int j=0; j<other.cards.size(); j++)
                assert(!cards[i].equals(other.cards[j]));

        if (category>other.category) return 1;
        else if (category==other.category)
            return betterCards(other);
        else return 2;

        ClassInv();//Invariant holds
    }
};

///\brief Just reads input and calls Hand functions
///
///@param[in] argc: nuber of parameters on the command line:\n
///@param[in] argv: holds parameters passed on the commend line:\n
int main(int argc, char** argv) {
    // parse command line
    char* ranks="23456789XJQKA";
    char* suits="SCDH";

    std::vector<int> par;
    for (int i=1;i<argc;i++) {
        for (int j=0;j<13;j++) {
            if (ranks[j]==argv[i][0]) par.push_back(j);
        }
        for (int j=0;j<4;j++) {
            if (suits[j]==argv[i][1]) par.push_back(j);
        }
    }

    bool unique=true;
    //looking for duplicates
    for (unsigned int i=0;i<par.size()/2;i++) {
        for (unsigned int j=i;j<par.size()/2;j++) {
            if (i!=j && par[2*j]==par[2*i] && par[2*j+1]==par[2*i+1]) {
                unique=false;
                std::cout<<"\n*****\nDuplicated playcards!\n*****\n\n";
            }
        }
    }

    if (!unique || (argc!=6 && argc!=11) ||(par.size()!=10 && par.size()!=20)) {
        std::cout<<"Wrong parameters!\n";
        std::cout<<"Command line parameters:\n";
        std::cout<<"five or ten different playcards\n";
        std::cout<<"Ranks: 2 3 4 5 6 7 8 9 X J Q K A\n";
        std::cout<<"Suits: S C D H\n\n";
        std::cout<<"example: ./poker XC 2H 3H 4D AS\n";
        std::cout<<"example: ./poker 8C 7D 6S 4D 5S   7S 2S 5D 8S 6C\n";
        exit(0);
    }

    PokerHand hand=PokerHand(par[0],par[1],par[2],par[3],par[4],par[5],par[6],par[7],par[8],par[9]);
    hand.print();

    //generating a random hand (non duplicate cards)
    std::vector<int> par2;
    srand(time(0));
    while (par2.size()!=10) {
        int r=rand()%13;
        int s=rand()%4;
        bool unique2=true;
        //no duplicates in the random hand
        for (int j=0;j<5;j++) {
            if (par[2*j]==r && par[2*j+1]==s)
                unique2=false;
        }
        //no duplicates between the hands
        for (unsigned int j=0;j<par2.size()/2;j++) {
            if (par2[2*j]==r && par2[2*j+1]==s)
                unique2=false;
        }
        if (unique2) {
            par2.push_back(r);
            par2.push_back(s);
        }
    }

    int res;
    if (par.size()==20) { //both Hands from Command Line
        PokerHand hand2=PokerHand(par[10],par[11],par[12],par[13],par[14],par[15],par[16],par[17],par[18],par[19]);
        hand2.print();
        res=hand.wins(hand2);
    } else { //random second Hand
        PokerHand hand3=PokerHand(par2[0],par2[1],par2[2],par2[3],par2[4],par2[5],par2[6],par2[7],par2[8],par2[9]);
        hand3.print();
        res=hand.wins(hand3);
    }

    if (res==0) std::cout<<"TIE!\n";
    if (res==1) std::cout<<"YOU WIN!\n";
    if (res==2) std::cout<<"YOU LOSE!\n";

    return 0;
}

