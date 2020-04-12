-------------------------- MODULE Leaderless_paxos --------------------------

EXTENDS Integers, TLAPS, TLC

CONSTANTS Acceptors, Values, Quorums, Proposers, Learners

VARIABLES msgs,    \* The set of messages that have been sent.
          maxBal,  \* maxBal[a] is the highest-number ballot acceptor a
                   \*   has participated in.
          maxVBal, \* maxVBal[a] is the highest ballot in which a has
          maxVal,  \*   voted, and maxVal[a] is the value it voted for 
                    \* in that ballot.
          learnt, \* learnt[l] is the value learnt by the learner l          
          state_time \* time of the system state
          
vars == <<msgs, maxBal, maxVBal, maxVal, learnt, state_time>>

None == CHOOSE v : v \notin Values

(***************************************************************************)
(*Ballots                                                                  *)
(***************************************************************************)
                      
Ballots == Nat

(***************************************************************************)
(*Time                                                                     *)
(***************************************************************************)
\* for now, representing time with natural numbers such as t_0, t_1, t_2,...
\* since using no other property but existence and greater than
\* time is discrete logical time
Time == Nat

\* If all acceptors in a quorum have each delivered a message at separate times, 
\* there will be a time when all acceptors in the quorum will have 
\* each delivered the message at a lower time
TemporalProperty1 ==
(
(\E Q \in Quorums : \A a \in Q : \E t \in Time : (state_time' = t) 
                              /\ (\E m \in msgs' :  (m.acc = a)))
=> (\E T \in Time : state_time' = T 
                /\ (\E Q \in Quorums : 
                     \A a \in Q : 
                      \E t \in Time : (T > t) 
                                   /\ (state_time' = t) 
                                   /\ (\E m \in msgs' : (m.acc = a))))
)

\* For all proposers, there is a time when no messages have been sent to or from it
TemporalProperty2 ==
\A P \in Proposers: 
(\E t \in Time :   state_time = t
                 /\ (~(\E m \in msgs : m.prop = P)))

\*if a new state X exist at a time t, then X is the current state at a time t2>t
TemporalProperty3 ==
/\(
    \A t \in Time:
     \A P \in Proposers:   
             (state_time' = t
           /\ (\E b \in Ballots: \E m \in msgs' : m.type = "1a" 
                                               /\ m.prop = P 
                                               /\ m.bal = b)
           /\ (~(\E m2 \in msgs': m2.type = "1b" /\ m2.prop = P))
           /\ (~(\E m2 \in msgs': m2.type = "2a" /\ m2.prop = P))
           /\ (~(\E m2 \in msgs': m2.type = "2b" /\ m2.prop = P))) 
     =>
      \E t2 \in Time:
             (t2>t
           /\ state_time = t2  
           /\ (\E b \in Ballots: \E m \in msgs : m.type = "1a" 
                                              /\ m.prop = P 
                                              /\ m.bal = b)
           /\ (~(\E m2 \in msgs: m2.type = "1b" /\ m2.prop = P))
           /\ (~(\E m2 \in msgs: m2.type = "2a" /\ m2.prop = P))
           /\ (~(\E m2 \in msgs: m2.type = "2b" /\ m2.prop = P))) 
  )
  
/\(
    \A t \in Time:
     \A P \in Proposers:   
         ((state_time' = t 
           /\ (\E b \in Ballots : 
               \E Q \in Quorums : 
                \A a \in Q : 
                 (\E m \in msgs' : (m.type = "1b") 
                                /\ (m.prop = P) 
                                /\ (m.acc = a) 
                                /\ (m.bal = b)))))
        =>
          (\E t2 \in Time:
                 (t2>t
               /\ state_time = t2  
               /\ (\E b \in Ballots : 
                   \E Q \in Quorums : 
                    \A a \in Q : 
                     (\E m \in msgs : (m.type = "1b") 
                                   /\ (m.prop = P) 
                                   /\ (m.acc = a) 
                                   /\ (m.bal = b)))))
  )                       

/\(
    \A t \in Time:
     \A P \in Proposers:   
         ((state_time' = t 
           /\ \E b \in Ballots : (\E Q \in Quorums : 
                                   \A a \in Q : 
                                    \E m \in msgs' : (m.type = "1b") 
                                                  /\ (m.bal = b)  
                                                  /\ (m.prop = P) 
                                                  /\ (m.acc = a)) 
                              /\ \E v \in Values : 
                                      (\E m \in msgs' : m.type = "2a" 
                                                     /\ m.prop = P 
                                                     /\ m.bal = b 
                                                     /\ m.val = v)))
        =>
          (\E t2 \in Time:
                 (t2>t
               /\ state_time = t2  
               /\ \E b \in Ballots : (\E Q \in Quorums : 
                                       \A a \in Q : 
                                        \E m \in msgs : (m.type = "1b") 
                                                     /\ (m.bal = b)  
                                                     /\ (m.prop = P) 
                                                     /\ (m.acc = a)) 
                                   /\ \E v \in Values : 
                                      (\E m \in msgs : m.type = "2a" 
                                                    /\ m.prop = P 
                                                    /\ m.bal = b 
                                                    /\ m.val = v)))
  )

/\(
    \A t \in Time:
     \A P \in Proposers:   
         ((state_time' = t 
           /\ \E v \in Values : (\E Q \in Quorums : 
                                  \A a \in Q : 
                                  (\E m \in msgs' : (m.type = "2b") 
                                                 /\ (m.val = v) 
                                                 /\ (m.acc = a)))))
        =>
          (\E t2 \in Time:
                 (t2>t
               /\ state_time = t2  
               /\ \E v \in Values : (\E Q \in Quorums : 
                                      \A a \in Q : 
                                       (\E m \in msgs : (m.type = "2b") 
                                                     /\ (m.val = v) 
                                                     /\ (m.acc = a)))))
  )


TemporalProperties == TemporalProperty1 
                   /\ TemporalProperty2 
                   /\ TemporalProperty3
-----------------------------------------------------------------------------

(***************************************************************************)
(*Predicates for message sending and delivery                              *)
(*                                 NOTE                                    *) 
(* Uniform Agreement: if one correct participant receives a message, then  *)
(*  all correct participants will eventually receive that message.         *)
(*  A single msgs variable shared by all agents suggests Uniform agreement *) 
(*                                                                         *)
(***************************************************************************)
\*A message that is eventually Delivered is added to msgs
\* A single msgs variable also asserts that if a message is delivered, 
\* it is delivered to all acceptors at the same time. 
Deliver(m,t) ==  (m.dTime = t) /\ (state_time' = t) /\ (msgs' = msgs \cup {m}) 

\*A message that is sent may or may not be delivered (May get lost)   
Send(m,t) ==  
              \/  \E t2 \in Time : (t2 > t) /\ Deliver(m,t2)  
              \/  \A t2 \in Time : ~ Deliver(m,t2 )
            
(***************************************************************************)
(* Phase 1a: A leader selects a ballot number b and sends a 1a message     *)
(* with ballot b to a majority of acceptors.  It can do this only if it    *)
(* has not already sent a 1a message for ballot b.                         *)
(***************************************************************************)

Phase1a(p,b,t ) ==               
      /\ \E t2 \in Time : (t2 >= t 
                        /\ Send([type |-> "1a", prop |-> p, bal |-> b], t2))
      /\ UNCHANGED <<maxVBal, maxBal, maxVal>>

             
(***************************************************************************)
(* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
(* than that of any 1a message to which it has already responded, then it  *)
(* responds to the request with a promise not to accept any more proposals *)
(* for ballots numbered less than b and with the highest-numbered ballot   *)
(* (if any) for which it has voted for a value and the value it voted for  *)
(* in that ballot.  That promise is made in a 1b message.                  *)
(***************************************************************************)
Phase1b(a,m,t) == 
 /\ \E t2 \in Time : ( t2 >= t
                   /\ Send([type |-> "1b", prop |-> m.prop, bal |-> m.bal, 
                           maxVBal |-> maxVBal[a], 
       maxVal |-> maxVal[a], acc |-> a], t2)
                   /\ maxBal' = [maxBal EXCEPT ![a] = m.bal] )
 /\ UNCHANGED <<maxVBal, maxVal>>

(***************************************************************************)
(* Phase 2a: If the leader receives a response to its 1b message (for      *)
(* ballot b) from a quorum of acceptors, then it sends a 2a message to all *)
(* acceptors for a proposal in ballot b with a value v, where v is the     *)
(* value of the highest-numbered proposal among the responses, or is any   *)
(* value if the responses reported no proposals.  The leader can send only *)
(* one 2a message for any ballot.                                          *)
(***************************************************************************)
Phase2a(p,b,v,t) ==
/\ \E t2 \in Time : (t2 >= t /\ Send([type |-> "2a", prop |-> p, 
                                      bal |-> b, val |-> v], t2))
/\ UNCHANGED <<maxBal, maxVBal, maxVal>>
(***************************************************************************)
(* Phase 2b: If an acceptor receives a 2a message for a ballot numbered    *)
(* b, it votes for the message's value in ballot b unless it has already   *)
(* responded to a 1a request for a ballot number greater than or equal to  *)
(* b.                                                                      *)
(***************************************************************************)
Phase2b(a,m,t) == 
    /\ \E t2 \in Time :
           ( t2 >= t
             /\ Send([type |-> "2b", prop |-> m.prop, bal |-> m.bal, 
                      val |-> m.val, acc |-> a], t2)
             /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
             /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
             /\ maxVal' = [maxVal EXCEPT ![a] = m.val] )
                 

(***************************************************************************)
(* Learning: If 2b messages for a value v are delivered from a quorum      *)
(* then any available learner will learn the value v                       *)
(***************************************************************************)
Learning(l,v,t) == 
    /\ \E t2 \in Time :
           ( t2 >= t
             /\ learnt' = [learnt EXCEPT ![l] = v]) 
                            
(***************************************************************************)
(*  The type of possible messages                                          *)
(***************************************************************************)
Messages ==    [type : {"1a"}, prop : Proposers, bal : Ballots, dTime : Time]
          \cup [type : {"1b"}, prop : Proposers, bal : Ballots, 
                maxVBal : Ballots \cup {-1}, maxVal : Values \cup {None}, 
                acc : Acceptors, dTime : Time]
            \cup [type : {"2a"}, prop : Proposers, bal : Ballots, 
                  val : Values, dTime : Time]
            \cup [type : {"2b"}, prop : Proposers, bal : Ballots, 
                  val : Values, acc : Acceptors, dTime : Time]       
-----------------------------------------------------------------------------

(***************************************************************************)
(*  The following section specifies rules and predicates that define       *)
(*  availability and the behaviour of available agents                     *)
(***************************************************************************)
\*Available
Available(x,t) == TRUE \/ FALSE
\*Always Available
Always_available(x) == \A t \in Time : Available(x,t)

\*All proposers are always available
All_proposers_always_available ==  \A p \in Proposers : Always_available(p)

\* A specific quorum is always available
Quorum_always_available == \E Q \in Quorums : \A a \in Q : Always_available(a)

\* A learner is always available
Learner_always_available == \E l \in Learners : Always_available(l)


\* Rules that govern when an action can happen
\* of the general form:
\* Preconditions => Preconditions /\ Action

Rule_1a_msg(p) == 
(\E b \in Ballots :
   (~ \E m \in msgs : m.type = "1a" /\ m.prop = p /\ m.bal = b) )   
                   => (  \E b \in Ballots :
                          /\ (~ \E m \in msgs : (m.type = "1a") 
                                             /\ (m.bal = b) ) 
                          /\  \E t1 \in Time : Phase1a(p,b,t1) )  

Rule_2a_msg(p) ==
( \E b \in Ballots :
  (\E Q \in Quorums : 
   \A a \in Q : 
    \E m \in msgs : 
       (m.type = "1b") /\ (m.bal = b)  /\ (m.prop = p) /\ (m.acc = a)))       
=> 
(  \E b \in Ballots :
  (\E Q \in Quorums : 
     \A a \in Q : 
      \E m \in msgs : 
         (m.type = "1b") /\ (m.bal = b)  /\ (m.prop = p) /\ (m.acc = a))
  /\ \E t2 \in Time : 
        \E v \in Values : 
            Phase2a(p,b,v,t2)                                           
)

(***************************************************************************)
(*Rules for Acceptors for Phase1b                                          *)
(***************************************************************************)
\*a - if there is only one distinct "1a" message
Only_single_1a(a) ==
((*a*)   
(     (\E m \in msgs : (m.type = "1a") /\ m.bal > maxBal[a])
  /\ ~(\E m1, m2 \in msgs : (~(m1=m2)) /\ (m1.type = "1a") /\ (m2.type = "1a")))
=> 
(\E m \in msgs : (m.type = "1a") /\ m.bal > maxBal[a] 
                                   /\ \E t \in Time : Phase1b(a,m,t))  
)(*a*)

\*b - two 1a msgs arrived at the same time
Multi_1a_simultaneous(a) ==
((*b*)
\A P1,P2 \in Proposers :
( (~(P1=P2)) 
  /\ \E m1, m2 \in msgs :  (m1.type = "1a") 
                        /\ (m1.prop = P1) 
                        /\ (m2.type = "1a") 
                        /\ (m2.prop = P2) 
                        /\ (m1.bal>m2.bal) 
                        /\ (m1.dTime = m2.dTime) 
                        /\ (m1.bal > maxBal[a]))
=>
( (~(P1=P2))
  /\ \E m1, m2 \in msgs : (m1.type = "1a") 
                       /\ (m1.prop = P1) 
                       /\ (m2.type = "1a") 
                       /\ (m2.prop = P2) 
                       /\ (m1.bal>m2.bal) 
                       /\ (m1.dTime = m2.dTime) 
                       /\ (m1.bal > maxBal[a])
                       /\ \E t \in Time : Phase1b(a,m1,t))
)(*b*)

\*b - two 1a msgs arrived at the same time
Multi_1a_non_simultaneous(a) ==
((*b*)
\A P1,P2 \in Proposers :
( (~(P1=P2)) 
  /\ \E m1, m2 \in msgs :  (m1.type = "1a") 
                        /\ (m1.prop = P1) 
                        /\ (m2.type = "1a") 
                        /\ (m2.prop = P2) 
                        /\ (m1.dTime < m2.dTime) 
                        /\ (m1.bal > maxBal[a]))
=>
( (~(P1=P2))
  /\ \E m1, m2 \in msgs :   (m1.type = "1a") 
                         /\ (m1.prop = P1) 
                         /\ (m2.type = "1a") 
                         /\ (m2.prop = P2) 
                         /\ (m1.dTime < m2.dTime) 
                         /\ (m1.bal > maxBal[a])
                         /\ \E t \in Time : Phase1b(a,m1,t))
)(*b*)

\* Highest proposal
General_1b_msg(a) ==
(
\A P \in Proposers: \A b \in Ballots :
(\E m \in msgs : (m.type = "1a") 
               /\ m.bal > maxBal[a] 
               /\ m.prop = P 
               /\ m.bal = b)
=> 
(\E m \in msgs : (m.type = "1a") 
               /\ m.bal > maxBal[a] 
               /\ m.prop = P /\ m.bal = b
               /\ \E t1 \in Time : Phase1b(a,m,t1))
)

Rule_1b_msg(a) ==  /\ Only_single_1a(a)
                   /\ Multi_1a_simultaneous(a)
                   /\ Multi_1a_non_simultaneous(a)
                   /\ General_1b_msg(a)

(***************************************************************************)
(*Rules for Acceptors for Phase2b                                          *)
(***************************************************************************)
                                             
Rule_2b_msg(a) == 
\A v \in Values :
    (( \E m \in msgs : 
       /\ (m.type = "2a")
       /\ (m.bal >= maxBal[a])
       /\ (m.val = v))
                            =>   ( \E m \in msgs : 
                                       /\ (m.type = "2a")
                                       /\ (m.bal >= maxBal[a])
                                       /\ (m.val = v)
                                       /\ \E t \in Time : Phase2b(a,m,t)))

(***************************************************************************)
(*Rules for Learners after Phase2b                                         *)
(***************************************************************************)

Rule_learner(l) ==
\A v \in Values :
 ((\E Q \in Quorums : \A a \in Q : (\E m \in msgs : (m.type = "2b") 
                                                 /\ (m.val = v) 
                                                 /\ (m.acc = a)))
  => \E t \in Time : Learning(l,v,t))
  
(***************************************************************************)
(*Non-Byzantine behavior of agents                                         *)
(***************************************************************************) 

\*A proposers's expected behavior                                       
Proposer_behaviour == 
(\A p \in Proposers : 
      (\E t \in Time : Available(p,t)) =>    /\ Rule_1a_msg(p)                                                                                                          
                                             /\ Rule_2a_msg(p) )

\*An acceptor's expected behavior
Acceptor_behaviour == 
(\A a \in Acceptors : Always_available(a)  => /\ Rule_1b_msg(a)  
                                              /\ Rule_2b_msg(a) ) 
                                              
\*A learner's expected behavior
Learner_behaviour == 
(\A l \in Learners : Always_available(l)  =>  Rule_learner(l))  
                                                    
-----------------------------------------------------------------------------                      
(***************************************************************************)
(*The following section specifies assumptions for proving progress         *)
(***************************************************************************)
            

\*A message that is eventually sent is eventually Delivered
aDelivery == 
    \* 1a msg
 /\  \A b \in Ballots :\A t \in Time : \A p \in Proposers : 
        Send([type |-> "1a", prop |-> p, bal |-> b], t) => 
           \E t2 \in Time : (t2 > t) /\ Deliver([type |-> "1a", prop |-> p, 
                                                 bal |-> b],t2)                         

     \* 1b msg
 /\  \A Q \in Quorums :  \A a \in Q : \A m \in msgs : 
                         \A t \in Time : Send([type |-> "1b", prop |-> m.prop, 
                                               bal |-> m.bal, maxVBal |-> maxVBal[a], 
                                               maxVal |-> maxVal[a], acc |-> a], t)       
      => 
          \E t2 \in Time : (t2 > t) /\ Deliver([type |-> "1b", prop |-> m.prop, 
                                                bal |-> m.bal, 
                 maxVBal |-> maxVBal[a], maxVal |-> maxVal[a], acc |-> a], t2)
 
    \* 2a msg
 /\ \A b \in Ballots : \A v \in Values : \A p \in Proposers :
             \A t \in Time : Send([type |-> "2a", prop |-> p, bal |-> b, 
                                   val |-> v], t)
      =>  
          \E t1 \in Time : (t1 > t) /\ Deliver([type |-> "2a", prop |-> p, 
                                                bal |-> b, val |-> v], t1)                  

    \* 2b msg
 /\  \A Q \in Quorums : \A a \in Q : \A t \in Time : \A m \in msgs :
        Send([type |-> "2b", prop |-> m.prop, bal |-> m.bal, val |-> m.val, 
              acc |-> a], t)
      =>   
          \E t1 \in Time : (t1 > t) 
                        /\ Deliver([type |-> "2b", prop |-> m.prop, 
                                    bal |-> m.bal, val |-> m.val, 
                                    acc |-> a], t1) 
         
         
\*All proposal numbers are unique
aUniqueProps ==
(\A m1, m2 \in msgs : (~(m1.prop = m2.prop)) => (~(m1.bal=m2.bal)) )           

\*A particular proposer cannot send more than one "1a" message
aPropLimit ==
\A m1, m2 \in msgs : ((m1.prop=m2.prop) => (m1.bal=m2.bal))
                
\*All agents behave as expected
aBehavior  == /\ Proposer_behaviour
              /\ Acceptor_behaviour
              /\ Learner_behaviour

\*Cardinality assumptions
aNonEmpty ==  (Ballots # {}) \* SInce a proposer has proposed 
                             \* the highest ballot, there is at least one ballot
 

\*The type invariant which assumes that all variables are always of the correct type
aTypeOk == /\ msgs \in SUBSET Messages
           /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
           /\ maxBal \in  [Acceptors -> Ballots \cup {-1}]
           /\ maxVal \in  [Acceptors -> Values \cup {None}]
           /\ \A a \in Acceptors : maxBal[a] >= maxVBal[a]
           /\ \A Q \in Quorums : \A a \in Q : a \in Acceptors
           /\ TemporalProperties
 
(***************************************************************************)
(*Follwing assumptions are consequences of finite number of proposers,     *)
(*unique Proposals, and proposal limit                                     *)
(***************************************************************************)               
\* A highest proposer is such that there is no other distinct proposer which has
\* proposed an equal or higher ballot
HighestProposer(P) == 
~(\E P2 \in Proposers :
         ~(P2=P) 
         /\ \E m, m2 \in msgs : (m.prop = P) /\ (m2.prop = P2) /\ (m2.bal >= m.bal) )

ThereExistsHighestProp == 
\E P \in Proposers : HighestProposer(P)

\* If no acceptor has sent a "1b" message to the highest proposer yet,
\* then the highest ballot any acceptor has responded to is
\* less than the ballot proposed by the highest proposer
HighestProposerAssertion1 ==
\A P \in Proposers :
  ( HighestProposer(P) =>  
      ( \A b \in Ballots :
        (      (\E m1 \in msgs : m1.type = "1a" /\ m1.prop = P /\ m1.bal = b)
           /\ ~(\E m2\in msgs : m2.type = "1b" /\ m2.prop = P /\ m2.bal = b)) 
            => (\A a \in Acceptors : \E m1 \in msgs : m1.type = "1a" 
                                                   /\ m1.prop = P 
                                                   /\ m1.bal = b 
                                                   /\ maxBal[a]<b)  
      ) )
                            
\* The maximum ballot seen by an acceptor is always less than or equal to the highest ballot                                       
HighestProposerAssertion2 ==
\A P \in Proposers :
  ( HighestProposer(P) =>  ( (\E m1 \in msgs :  m1.type = "2a" /\ (m1.prop = P)) 
                               => (\A a \in Acceptors : 
                                    \E m1 \in msgs : m1.type = "2a" 
                                                  /\ m1.prop = P 
                                                  /\ maxBal[a]<=m1.bal)
                           ) )    
HighestAssertions == 
                     /\ \E P \in Proposers : HighestProposer(P)
                     /\ HighestProposerAssertion1
                     /\ HighestProposerAssertion2

-----------------------------------------------------------------------------

\*The highest proposer is always available
Highest_prop_always_available == 
 \A P \in Proposers : (HighestProposer(P) => Always_available(P))                     


\*All proposers and a specific quorum of acceptors are always available 
aAvailability == /\ Highest_prop_always_available 
                 /\ Quorum_always_available  
                 /\ Learner_always_available
                                 
                              
\*ENVELOPE - all Assumptions
Assumptions == 
            /\ aAvailability 
            /\ aBehavior
            /\ aDelivery 
            /\ aPropLimit 
            /\ aNonEmpty
            /\ HighestAssertions
            /\ aTypeOk                     
                     
-----------------------------------------------------------------------------               
(***************************************************************************)
(*The proof                                                                *)
(***************************************************************************)   
\* Lemma - for all proposers, if there exists a time such that the proposer 
\*P is available and 1a messages have not been delivered from P, then 1a 
\* msgs will eventually be delivered from P
LEMMA Lemma1 ==
\A P \in Proposers :
(
    (\E t \in Time : Available(P,t) 
                  /\ state_time = t 
                  /\ ~(\E m \in msgs : m.prop = P ))
    /\ Assumptions

 =>  
 (\E t2 \in Time : 
 state_time' = t2 
 /\ \E b \in Ballots : 
    (\E m \in msgs' : m.type = "1a" /\ m.prop = P /\ m.bal = b)
                       /\ (~(\E m2 \in msgs': m2.type = "1b" /\ m2.prop = P))
                       /\ (~(\E m2 \in msgs': m2.type = "2a" /\ m2.prop = P))
                       /\ (~(\E m2 \in msgs': m2.type = "2b" /\ m2.prop = P)) )              
)
<1> SUFFICES ASSUME NEW P \in Proposers,
                   (\E t \in Time : Available(P,t) 
                                 /\ state_time = t 
                                 /\ ~(\E m \in msgs : m.prop = P ))
                   /\ Assumptions
             PROVE (\E t2 \in Time : state_time' = t2 
                                               /\ \E b \in Ballots : 
                                                  (\E m \in msgs' : m.type = "1a" 
                                                                 /\ m.prop = P 
                                                                 /\ m.bal = b)
                                       /\ (~(\E m2 \in msgs': m2.type = "1b" 
                                                           /\ m2.prop = P))
                                       /\ (~(\E m2 \in msgs': m2.type = "2a" 
                                                           /\ m2.prop = P))
                                       /\ (~(\E m2 \in msgs': m2.type = "2b" 
                                                           /\ m2.prop = P)) )          
    OBVIOUS   
<1>1. aAvailability /\ aBehavior /\ aDelivery /\aNonEmpty
    BY DEF Assumptions
<1>1a.     (\E t \in Time : Available(P,t) 
                  /\ state_time = t 
                  /\ (~(\E m \in msgs : m.type = "1a" /\ m.prop = P))
                  /\ (~(\E m \in msgs: m.type = "1b" /\ m.prop = P))
                  /\ (~(\E m \in msgs: m.type = "2a" /\ m.prop = P))
                  /\ (~(\E m \in msgs: m.type = "2b" /\ m.prop = P)))
      OBVIOUS
<1>2. Proposer_behaviour
    BY <1>1 DEF aBehavior    
<1>2a. \E t \in Time : Available(P,t) /\ ~(\E b \in Ballots : 
                                            \E m \in msgs : m.type = "1a" 
                                                         /\ m.prop = P 
                                                         /\ m.bal = b)
                                      /\ (~(\E m \in msgs: m.type = "1b" 
                                                        /\ m.prop = P))
                                      /\ (~(\E m \in msgs: m.type = "2a" 
                                                        /\ m.prop = P))
                                      /\ (~(\E m \in msgs: m.type = "2b" 
                                                        /\ m.prop = P))                                        
    BY <1>1a 
<1>2b. \E t \in Time : Available(P,t) /\ \A b \in Ballots : 
                                          ~( \E m \in msgs : m.type = "1a" 
                                                          /\ m.prop = P 
                                                          /\ m.bal = b)
                                      /\ (~(\E m \in msgs: m.type = "1b" 
                                                        /\ m.prop = P))
                                      /\ (~(\E m \in msgs: m.type = "2a" 
                                                        /\ m.prop = P))
                                      /\ (~(\E m \in msgs: m.type = "2b" 
                                                        /\ m.prop = P))                                                                              
    BY <1>2a  
<1>2c. \E t \in Time : Available(P,t) /\ \E b \in Ballots : 
                                          ~( \E m \in msgs : m.type = "1a" 
                                                          /\ m.prop = P 
                                                          /\ m.bal = b)
                                      /\ (~(\E m \in msgs: m.type = "1b" 
                                                        /\ m.prop = P)) 
                                      /\ (~(\E m \in msgs: m.type = "2a" 
                                                        /\ m.prop = P))
                                      /\ (~(\E m \in msgs: m.type = "2b" 
                                                        /\ m.prop = P))                                                                              
    BY <1>2b, <1>1 DEF aNonEmpty                 
<1>3. \E t \in Time : Available(P,t) /\ \E b \in Ballots : 
                                         ~( \E m \in msgs : m.type = "1a" 
                                                         /\ m.prop = P 
                                                         /\ m.bal = b) 
                                                         /\ Rule_1a_msg(P)
                                     /\ (~(\E m \in msgs: m.type = "1b" 
                                                       /\ m.prop = P))  
                                      /\ (~(\E m \in msgs: m.type = "2a" 
                                                        /\ m.prop = P))
                                      /\ (~(\E m \in msgs: m.type = "2b" 
                                                        /\ m.prop = P))                                                                             
    BY <1>2, <1>2c DEF Proposer_behaviour    
<1>4. (  \E b \in Ballots : 
                          /\ (~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b) ) 
                          /\  \E t1 \in Time : Phase1a(P,b,t1) )
                          /\ (~(\E m \in msgs: m.type = "1b" /\ m.prop = P))
                          /\ (~(\E m \in msgs: m.type = "2a" /\ m.prop = P))
                          /\ (~(\E m \in msgs: m.type = "2b" /\ m.prop = P))                                                                  
    BY <1>3 DEF Rule_1a_msg                               
<1>5. (  \E b \in Ballots :
                          /\ (~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b) ) 
                          /\  \E t \in Time : Send([type |-> "1a", prop |-> P, 
                                                    bal |-> b], t) )
                          /\ (~(\E m \in msgs: m.type = "1b" /\ m.prop = P))
                          /\ (~(\E m \in msgs: m.type = "2a" /\ m.prop = P))
                          /\ (~(\E m \in msgs: m.type = "2b" /\ m.prop = P))                                                                  
    BY <1>4 DEF Phase1a 
<1>6. (  \E b \in Ballots :
                          /\ (~(\E m \in msgs: m.type = "1b" /\ m.prop = P))
                          /\ (~(\E m \in msgs: m.type = "2a" /\ m.prop = P))
                          /\ (~(\E m \in msgs: m.type = "2b" /\ m.prop = P))                                                                  
                          /\ (~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b) ) 
                          /\  \E t \in Time : Deliver([type |-> "1a", 
                                                       prop |-> P, bal |-> b], t) )
    BY <1>5, <1>1 DEF aDelivery 
<1>7. (  \E b \in Ballots :
                          /\ (~(\E m \in msgs: m.type = "1b" /\ m.prop = P))
                          /\ (~(\E m \in msgs: m.type = "2a" /\ m.prop = P))
                          /\ (~(\E m \in msgs: m.type = "2b" /\ m.prop = P))                                                                  
                          /\ (~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b) ) 
                          /\  \E t \in Time : state_time' = t 
                                           /\ msgs' = msgs \cup {[type |-> "1a", 
                                                                  prop |-> P, 
                                                                  bal |-> b]} )
    BY <1>6 DEF Deliver 
<1>7a. (  \E b \in Ballots :
                          /\ (~(\E m \in msgs: m.type = "1b" /\ m.prop = P))
                          /\ (~(\E m \in msgs: m.type = "2a" /\ m.prop = P))
                          /\ (~(\E m \in msgs: m.type = "2b" /\ m.prop = P))                                                                  
                          /\ (~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b) ) 
                          /\  \E t \in Time : state_time' = t 
                                           /\ msgs' = msgs \cup {[type |-> "1a", 
                                                                  prop |-> P, 
                                                                  bal |-> b]} 
                          /\ (~(\E m \in msgs': m.type = "1b" /\ m.prop = P))
                          /\ (~(\E m \in msgs': m.type = "2a" /\ m.prop = P))
                          /\ (~(\E m \in msgs': m.type = "2b" /\ m.prop = P)))                         

    BY <1>7     
<1>8. (  \E b \in Ballots :
                          /\ (~(\E m \in msgs: m.type = "1b" /\ m.prop = P))
                          /\ (~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b) ) 
                          /\  \E t \in Time : state_time' = t 
                                           /\ [type |-> "1a", prop |-> P, 
                                               bal |-> b] \in msgs' 
                          /\ (~(\E m \in msgs': m.type = "1b" /\ m.prop = P))
                          /\ (~(\E m \in msgs': m.type = "2a" /\ m.prop = P))
                          /\ (~(\E m \in msgs': m.type = "2b" /\ m.prop = P)))                         
    BY <1>7a             
<1>9. (  \E b \in Ballots :
                          /\ (~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b) ) 
                          /\  \E t \in Time : state_time' = t 
                                           /\ \E m \in msgs' : m.type = "1a" 
                                                            /\ m.prop = P 
                                                            /\ m.bal = b
                          /\ (~(\E m \in msgs': m.type = "1b" /\ m.prop = P))
                          /\ (~(\E m \in msgs': m.type = "2a" /\ m.prop = P))
                          /\ (~(\E m \in msgs': m.type = "2b" /\ m.prop = P)))
    BY <1>8 
<1>10. \E t \in Time : state_time' = t /\ \E b \in Ballots : 
                                           \E m \in msgs' : m.type = "1a"  
                                                         /\ m.prop = P 
                                                         /\ m.bal = b
                                       /\ (~(\E m2 \in msgs': m2.type = "1b" 
                                                           /\ m2.prop = P))
                                       /\ (~(\E m2 \in msgs': m2.type = "2a" 
                                                           /\ m2.prop = P))
                                       /\ (~(\E m2 \in msgs': m2.type = "2b" 
                                                           /\ m2.prop = P))                                       
    BY <1>9                          
<1>200. QED
    BY <1>10
    
    
    
\* Lemma - for all proposers, there exist a time such that P is available 
\* and 1b messages from an available quorum have been delivered but 2a 
\* messages have not yet been delivered from P, then 2a messages 
\* from P will eventually be delivered
LEMMA Lemma2 ==
\A P \in Proposers :
(
    (\E t \in Time : Available(P,t) 
                  /\ state_time = t 
                  /\ \E b \in Ballots : 
                     (\E Q \in Quorums : 
                       \A a \in Q : 
                        \E m \in msgs : (m.type = "1b") 
                                     /\ (m.bal = b)  
                                     /\ (m.prop = P) 
                                     /\ (m.acc = a)))                  
 /\ Assumptions
 =>  
 (\E t2 \in Time : state_time' = t2 
                /\ \E b \in Ballots :  (\E Q \in Quorums : 
                                         \A a \in Q : 
                                          \E m \in msgs' : (m.type = "1b") 
                                                        /\ (m.bal = b)  
                                                        /\ (m.prop = P) 
                                                        /\ (m.acc = a)) 
                                     /\ \E v \in Values : 
                                         (\E m \in msgs' : m.type = "2a" 
                                                        /\ m.prop = P 
                                                        /\ m.bal = b 
                                                        /\ m.val = v))         
)    
<1> SUFFICES ASSUME NEW P \in Proposers,
                    (\E t \in Time : Available(P,t) 
                                  /\ state_time = t 
                                  /\ \E b \in Ballots : 
                                      (\E Q \in Quorums : 
                                         \A a \in Q : 
                                          \E m \in msgs : (m.type = "1b") 
                                                       /\ (m.bal = b)  
                                                       /\ (m.prop = P) 
                                                       /\ (m.acc = a)))                  
                 /\ Assumptions                   
             PROVE  (\E t2 \in Time : state_time' = t2 
                                                 /\ \E b \in Ballots :  
                                                    (\E Q \in Quorums : 
                                                      \A a \in Q : 
                                                       \E m \in msgs' : 
                                                              (m.type = "1b") 
                                                           /\ (m.bal = b)  
                                                           /\ (m.prop = P) 
                                                           /\ (m.acc = a))
                                                           /\ \E v \in Values : 
                                                              (\E m \in msgs' : 
                                                                   m.type = "2a" 
                                                                /\ m.prop = P 
                                                                /\ m.bal = b 
                                                                /\ m.val = v))   
    OBVIOUS
<1>1. aBehavior /\ aDelivery
    BY DEF Assumptions
<1>2. (\E t \in Time : Available(P,t) 
                  /\ state_time = t 
                  /\ \E b \in Ballots : 
                     (\E Q \in Quorums : 
                       \A a \in Q : 
                        \E m \in msgs : (m.type = "1b") 
                                     /\ (m.bal = b)  
                                     /\ (m.prop = P) 
                                     /\ (m.acc = a)))
    OBVIOUS
<1>3. (\E t \in Time : Available(P,t) 
                  /\ state_time = t 
                  /\ \E b \in Ballots : 
                     (\E Q \in Quorums : 
                       \A a \in Q : 
                        \E m \in msgs : (m.type = "1b") 
                                     /\ (m.bal = b)  
                                     /\ (m.prop = P) 
                                     /\ (m.acc = a))
                  /\ Rule_2a_msg(P))
    BY <1>2, <1>1 DEF aBehavior, Proposer_behaviour                                   
<1>4. (   \E b \in Ballots : 
          (\E Q \in Quorums : \A a \in Q : \E m \in msgs : (m.type = "1b") 
                                                        /\ (m.bal = b)  
                                                        /\ (m.prop = P) 
                                                        /\ (m.acc = a))
          /\ Rule_2a_msg(P))
    BY <1>3
<1>5. (  \E b \in Ballots : 
         (\E Q \in Quorums : \A a \in Q : \E m \in msgs : (m.type = "1b") 
                                                       /\ (m.bal = b)  
                                                       /\ (m.prop = P) 
                                                       /\ (m.acc = a))
              /\ \E t2 \in Time : \E v \in Values : Phase2a(P,b,v,t2) ) 
    BY <1>4 DEF Rule_2a_msg               
<1>6. (  \E b \in Ballots : 
        (\E Q \in Quorums : \A a \in Q : \E m \in msgs : (m.type = "1b") 
                                                      /\ (m.bal = b)  
                                                      /\ (m.prop = P) 
                                                      /\ (m.acc = a))
              /\ \E t2 \in Time : 
                  \E v \in Values :  
                    Send([type |-> "2a", prop |-> P, bal |-> b, val |-> v], t2)) 
    BY <1>5 DEF Phase2a 
<1>7. (  \E b \in Ballots : 
         (\E Q \in Quorums : \A a \in Q : \E m \in msgs : (m.type = "1b") 
                                                       /\ (m.bal = b)  
                                                       /\ (m.prop = P) 
                                                       /\ (m.acc = a))
              /\ \E t2 \in Time : 
                 \E v \in Values :  
                   Deliver([type |-> "2a", prop |-> P, bal |-> b, val |-> v], t2)) 
    BY <1>6, <1>1 DEF aDelivery
<1>8.  \E b \in Ballots : 
       (\E Q \in Quorums : \A a \in Q : \E m \in msgs : (m.type = "1b") 
                                                     /\ (m.bal = b)  
                                                     /\ (m.prop = P) 
                                                     /\ (m.acc = a))
              /\ \E t2 \in Time : 
                  \E v \in Values :  state_time' = t2 
                                  /\ msgs' = msgs \cup {[type |-> "2a", 
                                                         prop |-> P, bal |-> b, 
                                                         val |-> v]} 
    BY <1>7 DEF Deliver
<1>9.  \E b \in Ballots : 
       (\E Q \in Quorums : \A a \in Q : \E m \in msgs : (m.type = "1b") 
                                                     /\ (m.bal = b)  
                                                     /\ (m.prop = P) 
                                                     /\ (m.acc = a))
              /\ \E t2 \in Time : 
                  \E v \in Values : state_time' = t2 
                                 /\ [type |-> "2a", prop |-> P, bal |-> b, 
                                     val |-> v] \in msgs'     
    BY <1>8
<1>10.  \E b \in Ballots : 
        (\E Q \in Quorums : \A a \in Q : \E m \in msgs : (m.type = "1b") 
                                                      /\ (m.bal = b)  
                                                      /\ (m.prop = P) 
                                                      /\ (m.acc = a))
              /\ \E t2 \in Time : 
                  \E v \in Values :  state_time' = t2 
                                  /\ \E m \in msgs' : m.type = "2a" 
                                                   /\ m.prop = P 
                                                   /\ m.bal = b 
                                                   /\ m.val = v 
    BY <1>9 
<1>11.  \E t2 \in Time : state_time' = t2 /\ 
          \E b \in Ballots : (\E Q \in Quorums : 
             \A a \in Q : \E m \in msgs : (m.type = "1b") 
                                       /\ (m.bal = b)  
                                       /\ (m.prop = P) 
                                       /\ (m.acc = a))
                   /\ \E v \in Values : \E m \in msgs' : m.type = "2a" 
                                                      /\ m.prop = P 
                                                      /\ m.bal = b 
                                                      /\ m.val = v 
    BY <1>10
<1>12.  \E t2 \in Time : state_time' = t2  
         /\ \E b \in Ballots : (\E Q \in Quorums : 
               \A a \in Q : \E m \in msgs' : (m.type = "1b") 
                                          /\ (m.bal = b)  
                                          /\ (m.prop = P) 
                                          /\ (m.acc = a))
                            /\ \E v \in Values : \E m \in msgs' : m.type = "2a" 
                                                               /\ m.prop = P 
                                                               /\ m.bal = b 
                                                               /\ m.val = v 
    BY <1>11, <1>8                         
<1>200. QED
    BY <1>12    
                    
\* Lemma - If a proposer has received "1b" messages from a quorum for its proposal number,
\* and a "2a" messages from the proposer for the proposal number has been delivered
\* it will receive 2b messages from a quorum if in all quorums, there is no acceptor 
\* which has responded to a higher numbered proposal 
LEMMA Lemma3 ==
\A P1 \in Proposers:
(
  (\E t \in Time : state_time = t
  /\ \E b \in Ballots : (\E Q \in Quorums : 
                         \A a \in Q : 
                          \E m \in msgs : (m.type = "1b") 
                                       /\ (m.bal = b)  
                                       /\ (m.prop = P1) 
                                       /\ (m.acc = a))
                     /\ \E v \in Values : (\E m \in msgs : (m.type = "2a") 
                                                        /\ (m.prop = P1) 
                                                        /\ (m.bal = b) 
                                                        /\ (m.val = v))
                     /\ (\A Q \in Quorums : \A a \in Q: (maxBal[a]<=b) ))
  /\ Assumptions                   
     =>(\E t \in Time : state_time' = t 
                     /\ \E v \in Values :
                         (\E Q \in Quorums : 
                          \A a \in Q : 
                           (\E m \in msgs' : 
                             (m.type = "2b") /\ (m.val = v) /\ (m.acc = a))))
)
<1> SUFFICES ASSUME NEW P1 \in Proposers,
                        (\E b \in Ballots : 
                          (\E Q \in Quorums : \A a \in Q : 
                                                \E m \in msgs : (m.type = "1b") 
                                                             /\ (m.bal = b) 
                                                             /\ (m.prop = P1)
                                                             /\ (m.acc = a))
                                         /\ \E v \in Values : 
                                                 (\E m \in msgs : (m.type = "2a") 
                                                               /\ (m.prop = P1) 
                                                               /\ (m.bal = b) 
                                                               /\ (m.val = v))
                                         /\ (\A Q \in Quorums :
                                               \A a \in Q: (maxBal[a]<=b) ))
                        /\ Assumptions   
                    PROVE (\E t \in Time : state_time' = t 
                                        /\ \E v \in Values : 
                                           (\E Q \in Quorums : 
                                             \A a \in Q : 
                                              (\E m \in msgs' : (m.type = "2b") 
                                                             /\ (m.val = v) 
                                                             /\ (m.acc = a))))
    OBVIOUS         
<1>1. \E b \in Ballots : 
                      /\ (\E Q \in Quorums : \A a \in Q : 
                                             \E m \in msgs :  (m.type = "1b") 
                                                           /\ (m.bal = b) 
                                                           /\ (m.prop = P1)
                                                           /\ (m.acc = a))
                      /\ \E v \in Values : (\E m \in msgs : (m.type = "2a") 
                                                           /\ (m.prop = P1) 
                                                           /\ (m.bal = b) 
                                                           /\ (m.val = v))
                      /\ (\A Q \in Quorums : \A a \in Q: (maxBal[a]<=b) )     
    OBVIOUS
<1>2. ASSUME (~(\E v \in Values : \E Q \in Quorums : \A a \in Q : 
                                    \E m \in msgs' : \E t \in Time : 
                                       (state_time' = t) 
                                    /\ (m.type = "2b") /\ (m.val = v) /\ (m.acc = a)))
      PROVE FALSE
     <2>1. (~(\E v \in Values : \E Q \in Quorums : \A a \in Q : 
                                  \E t \in Time : (state_time' = t) 
                                               /\ (\E m \in msgs' : (m.type = "2b") 
                                                                 /\ (m.val = v) 
                                                                 /\ (m.acc = a))))
          BY <1>2
     <2>2. aAvailability /\ aTypeOk
          BY DEF Assumptions
     <2>3. aBehavior     
          BY DEF Assumptions
     <2>4. \A Q \in Quorums: \A a \in Q : a \in Acceptors
          BY <2>2 DEF aTypeOk
     <2>5. \E Q \in Quorums : \A a \in Q : Always_available(a)
          BY <2>2 DEF aAvailability, Quorum_always_available 
     <2>6. \E Q \in Quorums : \A a \in Q : Rule_2b_msg(a)
          BY <2>3, <2>4, <2>5 DEF aBehavior, Acceptor_behaviour 
     <2>7. \E b \in Ballots : 
                          /\ \E v \in Values : (\E m \in msgs : (m.type = "2a") 
                                                             /\ (m.prop = P1) 
                                                             /\ (m.bal = b) 
                                                             /\ (m.val = v))     
                          /\ \E Q \in Quorums : \A a \in Q : Rule_2b_msg(a) 
                                                          /\ (maxBal[a]<=b) 
          BY <2>6, <1>1
     <2>7a. aTypeOk
          BY DEF Assumptions
     <2>7b. msgs \in SUBSET Messages
          BY <2>7a DEF aTypeOk
     <2>7c. \A m \in msgs : m.bal \in Nat
          BY <2>7b DEF Messages, Ballots                       
     <2>8. \E b \in Ballots : \E v \in Values :     
                          \E Q \in Quorums : \A a \in Q :
                                                Rule_2b_msg(a) 
                                             /\ (maxBal[a]<=b)
                                             /\ (\E m \in msgs : (m.type = "2a") 
                                                              /\ (m.prop = P1) 
                                                              /\ (m.bal = b) 
                                                              /\ (m.val = v))      
          BY <2>7  
     <2>9. \E b \in Ballots : \E v \in Values :     
              \E Q \in Quorums : \A a \in Q :
                                        Rule_2b_msg(a)  
                                     /\ \E m \in msgs : (m.type = "2a") 
                                                     /\ (m.prop = P1) 
                                                     /\ (m.bal = b) 
                                                     /\ (m.val = v) 
                                                     /\ (maxBal[a]<=m.bal)      
      BY <2>8  
     <2>10. \E v \in Values :
            \E Q \in Quorums : \A a \in Q :
                                           Rule_2b_msg(a)  
                                         /\ \E m \in msgs : (m.type = "2a") 
                                                         /\ (m.val = v) 
                                                         /\ (maxBal[a]<=m.bal)      
          BY <2>9
     <2>11. \E v \in Values : \E Q \in Quorums : \A a \in Q :
                                           Rule_2b_msg(a)  
                                         /\ \E m \in msgs : (m.type = "2a") 
                                                         /\ (m.val = v) 
                                                         /\ (maxBal[a]<=m.bal)      
                                         /\ \E t \in Time : Phase2b(a,m,t)
          BY <2>10 DEF Rule_2b_msg                               
     <2>12. \E v \in Values : 
             \E Q \in Quorums : \A a \in Q :
                       Rule_2b_msg(a)  
                     /\ \E m \in msgs : (m.type = "2a") 
                                     /\ (m.val = v) 
                                     /\ (maxBal[a]<=m.bal)      
                     /\ \E t \in Time : Send([type |-> "2b", prop |-> m.prop, 
                                              bal |-> m.bal, val |-> m.val, 
                                              acc |-> a], t)
          BY <2>11 DEF Phase2b
     <2>12a. aDelivery
          BY DEF Assumptions     
     <2>13. \E v \in Values : 
             \E Q \in Quorums : \A a \in Q :
                   Rule_2b_msg(a)  
                 /\ \E m \in msgs : (m.type = "2a") 
                                 /\ (m.val = v) 
                                 /\ (maxBal[a]<=m.bal)      
                 /\ \E t \in Time : Deliver([type |-> "2b", prop |-> m.prop, 
                                             bal |-> m.bal, 
                                             val |-> m.val, acc |-> a], t)
          BY <2>12, <2>12a DEF aDelivery
     <2>14. \E v \in Values : 
             \E Q \in Quorums : \A a \in Q :
                           Rule_2b_msg(a)  
                         /\ \E m \in msgs : (m.type = "2a") 
                                         /\ (m.val = v) 
                                         /\ (maxBal[a]<=m.bal)      
                         /\ \E t \in Time : Deliver([type |-> "2b", 
                                                     prop |-> m.prop, 
                                                     bal |-> m.bal, 
                                                     val |-> m.val, 
                                                     acc |-> a], t)
          BY <2>13
     <2>15. \E v \in Values : 
             \E Q \in Quorums : 
              \A a \in Q : \E m \in msgs : 
                                         (m.type = "2a") 
                                      /\ (m.val = v) 
                                      /\ (maxBal[a]<=m.bal)      
                                      /\ \E t \in Time :
                                            /\ (state_time' = t) 
                                            /\ msgs' = msgs \cup {[type |-> "2b", 
                                                                   prop |-> m.prop, 
                                                                   bal |-> m.bal, 
                                                                   val |-> m.val, 
                                                                   acc |-> a]}
          BY <2>13 DEF Deliver
     <2>15a.  \A Q \in Quorums: \A a \in Q: \A m \in msgs : \A t \in Time :
            ((msgs' = msgs \cup {[type |-> "2b", prop |-> m.prop, 
                                  bal |-> m.bal, val |-> m.val, acc |-> a]})
            => ([type |-> "2b", prop |-> m.prop, bal |-> m.bal, 
                 val |-> m.val, acc |-> a] \in msgs'))
            OBVIOUS                    
     <2>16. \E v \in Values : 
             \E Q \in Quorums : \A a \in Q : 
              \E m \in msgs : 
                         (m.type = "2a") 
                      /\ (m.val = v) 
                      /\ (maxBal[a]<=m.bal)      
                      /\ \E t \in Time :
                            /\ (state_time' = t) 
                            /\ [type |-> "2b", prop |-> m.prop, bal |-> m.bal, 
                                val |-> m.val, acc |-> a] \in msgs'
          BY <2>15, <2>15a
     <2>17. \E v \in Values : 
             \E Q \in Quorums : 
              \A a \in Q : 
               \E m \in msgs : 
                             (m.type = "2a") 
                          /\ (m.val = v) 
                          /\ (maxBal[a]<=m.bal)      
                          /\ \E t \in Time :
                                /\ (state_time' = t) 
                                /\ \E m2 \in msgs' : (m2.type = "2b") 
                                                  /\ (m2.val = m.val) 
                                                  /\ (m2.acc = a)
          BY <2>16
     <2>18. \E v \in Values : 
             \E Q \in Quorums : 
              \A a \in Q :  
               \E t \in Time : (state_time' = t) 
                            /\ (\E m2 \in msgs' : (m2.type = "2b") 
                                               /\ (m2.val = v) 
                                               /\ (m2.acc = a))
          BY <2>17          
     <2>200. QED
            BY <2>18, <2>1
<1>2a. TemporalProperties
     BY DEF Assumptions, aTypeOk  
<1>2i. TemporalProperty1
     BY <1>2a DEF TemporalProperties            
<1>3. (\E t \in Time : state_time' = t 
                    /\ \E v \in Values : 
                       (\E Q \in Quorums : 
                         \A a \in Q : (\E m \in msgs' : (m.type = "2b") 
                                                     /\ (m.val = v) 
                                                     /\ (m.acc = a))))
     BY <1>2, <1>2i DEF TemporalProperty1            
<1>200. QED
    BY <1>3
                    

                     
\* Theorem - If a proposer proposes the highest ballot and "1a" messages from it have been delivered
\* and it has not yet received any "1b" message, it will eventually receive "1b" messages from a 
\* quorum of acceptors                   
THEOREM Lemma4 ==
\A P \in Proposers:  
    HighestProposer(P)
  /\ (\E t \in Time : state_time = t 
  /\ \E b \in Ballots : \E m \in msgs : m.type = "1a" /\ m.prop = P /\ m.bal = b
  /\ (~(\E m2\in msgs : m2.type = "1b" /\ m2.prop = P /\ m2.bal = b)))
  /\ Assumptions
  =>
 (\E t \in Time : state_time' = t 
              /\ (\E b \in Ballots :
                  \E Q \in Quorums : 
                   \A a \in Q :  
                    (\E m \in msgs' : 
                     (m.type = "1b") /\ (m.prop = P) /\ (m.acc = a) /\ (m.bal = b))))
<1> SUFFICES ASSUME NEW P \in Proposers, 
                       HighestProposer(P)
                      /\ (\E t \in Time : state_time = t
                      /\ \E b \in Ballots : \E m \in msgs : m.type = "1a" 
                                                         /\ m.prop = P 
                                                         /\ m.bal = b
                      /\ (~(\E m2\in msgs : m2.type = "1b" /\ m2.prop = P/\ m2.bal = b)))
                      /\ Assumptions 
                      
            PROVE    (\E t \in Time : state_time' = t 
                                  /\ (\E b \in Ballots : 
                                       \E Q \in Quorums : 
                                        \A a \in Q : 
                                         (\E m \in msgs' : (m.type = "1b") 
                                                        /\ (m.prop = P) 
                                                        /\ (m.acc = a) 
                                                        /\ (m.bal = b))))
    OBVIOUS   
<1>1. HighestProposerAssertion1
    BY DEF Assumptions, HighestAssertions   
<1>2.         /\ HighestProposer(P)
              /\ \E b \in Ballots :
                  (/\ (\E m \in msgs : m.type = "1a" /\ m.prop = P /\ m.bal = b)
                  /\ (~(\E m2\in msgs : m2.type = "1b" /\ m2.prop = P /\ m2.bal = b)))
    OBVIOUS    
<1>3.        \A b \in Ballots :
                 ( (/\ (\E m \in msgs : m.type = "1a" /\ m.prop = P /\ m.bal = b)
                  /\ (~(\E m2\in msgs : m2.type = "1b" /\ m2.prop = P /\ m2.bal = b)))  
            =>(\A a \in Acceptors : \E m1 \in msgs : m1.type = "1a" 
                                                  /\ m1.prop = P  
                                                  /\ m1.bal = b 
                                                  /\ maxBal[a]<b) )
    BY <1>2, <1>1 DEF HighestProposerAssertion1         
<1>3a. aPropLimit /\ aTypeOk 
     BY DEF Assumptions                             
<1>4.      /\ HighestProposer(P)
              /\ \E b \in Ballots :
                  (/\ (\E m \in msgs : m.type = "1a" /\ m.prop = P /\ m.bal = b)
                  /\ (~(\E m2\in msgs : m2.type = "1b" /\ m2.prop = P /\ m2.bal = b)))
                  /\ (\A a \in Acceptors : \E m1 \in msgs : m1.type = "1a" 
                                                         /\ m1.prop = P  
                                                         /\ m1.bal = b 
                                                         /\ maxBal[a]<b)
    BY <1>3, <1>2    
<1>4a. \E b \in Ballots : \A a \in Acceptors : \E m1 \in msgs : m1.type = "1a" 
                                                             /\ m1.prop = P 
                                                             /\ m1.bal = b 
                                                             /\ maxBal[a]<m1.bal
    BY <1>4
<1>5. ASSUME (~(\E t \in Time : state_time' = t 
                             /\ \E b \in Ballots : 
                                (\E Q \in Quorums : 
                                  \A a \in Q : (\E m \in msgs' : (m.type = "1b") 
                                                              /\ (m.prop = P) 
                                                              /\ (m.acc = a) 
                                                              /\ (m.bal = b)))))
      PROVE FALSE
      <2>1.\E b \in Ballots : \A a \in Acceptors : \E m1 \in msgs : m1.type = "1a" 
                                                                 /\ m1.prop = P 
                                                                 /\ m1.bal = b 
                                                                 /\ maxBal[a]<m1.bal
          BY <1>4a
      <2>2. aDelivery /\ aBehavior /\ aAvailability /\ aTypeOk 
           BY DEF Assumptions
      <2>3. Quorum_always_available
           BY <2>2 DEF  aAvailability
      <2>4. \A Q \in Quorums : \A a \in Q : a \in Acceptors
           BY <2>2 DEF aTypeOk
      <2>5. \E Q \in Quorums : \A a \in Q : Always_available(a) /\ a \in Acceptors
           BY <2>3, <2>4 DEF Quorum_always_available
      <2>6. \E b \in Ballots : 
             \E Q \in Quorums : \A a2 \in Q : \E m1 \in msgs : m1.type = "1a" 
                                                            /\ m1.prop = P 
                                                            /\ maxBal[a2]<m1.bal 
                                                            /\ m1.bal = b
                                                            /\ Always_available(a2) 
                                                            /\ a2 \in Acceptors
           BY <2>5, <2>1
      <2>7. \E b \in Ballots : 
             \E Q \in Quorums : 
              \A a2 \in Q : \E m1 \in msgs : m1.type = "1a" 
                                          /\ m1.prop = P 
                                          /\ maxBal[a2]<m1.bal 
                                          /\ m1.bal = b 
                                          /\ Always_available(a2) /\ a2 \in Acceptors
           BY <2>6
      <2>8. \E b \in Ballots : 
             \E Q \in Quorums : 
              \A a2 \in Q : 
               \E m1 \in msgs : m1.type = "1a" 
                             /\ m1.prop = P 
                             /\ m1.bal = b 
                             /\ maxBal[a2]<m1.bal 
                             /\ Always_available(a2) /\ a2 \in Acceptors                                                       
           BY <2>7
      <2>8a. Acceptor_behaviour
           BY <2>2 DEF aBehavior 
      <2>8b.(\A a \in Acceptors : Always_available(a)  => /\ Rule_1b_msg(a)  \*behavior
                                                          /\ Rule_2b_msg(a) )
           BY <2>8a DEF Acceptor_behaviour          
      <2>9. \E b \in Ballots : \E Q \in Quorums : \A a2 \in Q : 
                     \E m1 \in msgs : m1.type = "1a" /\ m1.prop = P /\ m1.bal = b 
                                    /\ maxBal[a2]<m1.bal 
                                    /\ Always_available(a2)
                                    /\ Rule_1b_msg(a2)                                                        
           BY <2>8, <2>4, <2>8b
      <2>10. \E b \in Ballots : \E Q \in Quorums : \A a2 \in Q : 
                     \E m1 \in msgs : m1.type = "1a" /\ m1.prop = P /\ m1.bal = b  
                                    /\ maxBal[a2]<m1.bal 
                                    /\ Always_available(a2)
                                    /\ General_1b_msg(a2)                                                                   
           BY <2>9 DEF Rule_1b_msg
      <2>10a. msgs \in SUBSET Messages
           BY DEF Assumptions, aTypeOk
      <2>10b. \A m \in msgs :m.bal \in Nat
           BY <2>10a DEF Messages, Ballots     
      <2>11. \E b \in Ballots : \E Q \in Quorums : \A a2 \in Q : 
                     \E m1 \in msgs : m1.type = "1a" /\ m1.prop = P /\ m1.bal = b 
                                    /\ m1.bal>maxBal[a2] 
                                    /\ Always_available(a2)
                                    /\ General_1b_msg(a2)                                                                   
           BY <2>10, <2>10b DEF Nat           
      <2>11a. (\E b \in Ballots : \E Q \in Quorums : \A a2 \in Q : 
                     \E m1 \in msgs : m1.type = "1a" /\ m1.prop = P 
                                   /\ m1.bal = b /\ m1.bal>maxBal[a2])
              =>(\E Q \in Quorums : \A a2 \in Q : \E b \in Ballots : 
                     \E m1 \in msgs : m1.type = "1a" /\ m1.prop = P 
                                   /\ m1.bal = b /\ m1.bal>maxBal[a2])            
           OBVIOUS          
      <2>12. \E b \in Ballots : \E Q \in Quorums : \A a2 \in Q : 
                     \E m1 \in msgs : m1.type = "1a" /\ m1.prop = P /\ m1.bal = b 
                                    /\ m1.bal>maxBal[a2] 
                                    /\ Always_available(a2)
                                    /\ \E t1 \in Time : Phase1b(a2,m1,t1)
           BY <2>11, <2>11a DEF  General_1b_msg                                                                            
      <2>13. \E b \in Ballots : \E Q \in Quorums : \A a2 \in Q : 
                     \E m1 \in msgs : m1.type = "1a" /\ m1.prop = P /\ m1.bal = b 
                                   /\ \E t1 \in Time : Phase1b(a2,m1,t1)                                    
           BY <2>12 
      <2>14. \E b \in Ballots : \E Q \in Quorums : \A a \in Q : 
             \E m \in msgs : m.type = "1a" /\ m.prop = P /\ m.bal = b 
          /\ \E t \in Time : Send([type |-> "1b", prop |-> m.prop, 
                                   bal |-> m.bal, maxVBal |-> maxVBal[a], 
                                   maxVal |-> maxVal[a], acc |-> a],t)                                    
           BY <2>13 DEF Phase1b 
      <2>15.  \E b \in Ballots : \E Q \in Quorums : \A a \in Q : 
               \E m \in msgs : m.type = "1a" /\ m.prop = P /\ m.bal = b
            /\ \E t \in Time : Deliver([type |-> "1b", prop |-> m.prop, 
                                        bal |-> m.bal, maxVBal |-> maxVBal[a], 
                                        maxVal |-> maxVal[a], acc |-> a],t)                                    
           BY <2>14, <2>2 DEF aDelivery
      <2>16.  \E b \in Ballots : \E Q \in Quorums : \A a \in Q : 
                 \E m \in msgs : m.type = "1a" /\ m.prop = P /\ m.bal = b
               /\ \E t \in Time : state_time' = t
                               /\ msgs' = msgs \cup {[type |-> "1b", 
                                                      prop |-> m.prop, 
                                                      bal |-> m.bal, 
                                                      maxVBal |-> maxVBal[a], 
                                                      maxVal |-> maxVal[a], 
                                                      acc |-> a]}                                  
       BY <2>15 DEF Deliver
      <2>16a.\A b \in Ballots : \A Q \in Quorums : \A a \in Q : 
                \A m \in msgs : \A t \in Time :
               ((msgs' = msgs \cup {[type |-> "1b", prop |-> m.prop, 
                                     bal |-> m.bal, maxVBal |-> maxVBal[a], 
                                     maxVal |-> maxVal[a], acc |-> a]})
               => [type |-> "1b", prop |-> m.prop, bal |-> m.bal, 
                   maxVBal |-> maxVBal[a], maxVal |-> maxVal[a], acc |-> a] \in msgs')
           OBVIOUS         
      <2>17. \E b \in Ballots : \E Q \in Quorums : \A a \in Q : 
              \E m \in msgs : m.type = "1a" /\ m.prop = P /\ m.bal = b
           /\ \E t \in Time : state_time' = t
                           /\ [type |-> "1b", prop |-> m.prop, bal |-> m.bal, 
                               maxVBal |-> maxVBal[a], maxVal |-> maxVal[a], 
                               acc |-> a] \in msgs'                                  
           BY <2>16, <2>16a
      <2>18. \E b \in Ballots : \E Q \in Quorums : \A a \in Q : 
              \E m \in msgs : m.type = "1a" /\ m.prop = P /\ m.bal = b
           /\ \E t \in Time : state_time' = t
                           /\ \E m2 \in msgs' : m2.prop = P 
                                             /\ m2.acc= a 
                                             /\ m2.type = "1b" /\ m2.bal = b                                  
       BY <2>17
      <2>19. \E b \in Ballots : \E Q \in Quorums : \A a \in Q : 
           /\ \E t \in Time : state_time' = t
                             /\ \E m2 \in msgs' : m2.prop = P 
                                               /\ m2.acc= a 
                                               /\ m2.type = "1b" /\ m2.bal = b                                 
           BY <2>18
      <2>20.  \E b \in Ballots :  \E t \in Time : state_time' = t  
                                               /\ \E Q \in Quorums : \A a \in Q :    
                              \E m2 \in msgs' : m2.prop = P 
                                             /\ m2.acc= a 
                                             /\ m2.type = "1b" /\ m2.bal = b 
           BY <2>19, <1>3a DEF aTypeOk, TemporalProperties, TemporalProperty1                                                              
      <2>200. QED
           BY <1>5, <2>20
<1>5a. TemporalProperties
     BY DEF Assumptions, aTypeOk  
<1>6. TemporalProperty1
     BY <1>5a DEF TemporalProperties            
<1>7. (\E t \in Time : state_time' = t 
                   /\ (\E b \in Ballots : 
                        \E Q \in Quorums : 
                         \A a \in Q :  (\E m \in msgs' : (m.type = "1b") 
                                                      /\ (m.prop = P) 
                                                      /\ (m.acc = a) 
                                                      /\ (m.bal = b))))
     BY <1>5, <1>6 DEF TemporalProperty1
<1>200. QED
   BY <1>7  

\* Theorem - If a proposer proposes the highest ballot and has received "1b" messages from a quorum 
\* for its proposal number and "2a" messages from it have been delivered
\* it will eventually receive "2b" messages from a quorum of acceptors 
THEOREM Lemma5 ==
\A P \in Proposers:  
    HighestProposer(P)
  /\(\E t \in Time : state_time = t
  /\ \E b \in Ballots : (\E Q \in Quorums : 
                         \A a \in Q : 
                          \E m \in msgs : 
                            (m.type = "1b") /\ (m.bal = b)  
                         /\ (m.prop = P) /\ (m.acc = a))
                     /\ \E v \in Values : 
                         (\E m \in msgs : (m.type = "2a") /\ (m.prop = P) 
                                       /\ (m.bal = b) /\ (m.val = v)))
  /\ Assumptions
  =>
   (\E t \in Time : state_time' = t 
                 /\ \E v \in Values :
                    (\E Q \in Quorums : 
                      \A a \in Q : 
                      (\E m \in msgs' : 
                        (m.type = "2b") /\ (m.val = v) /\ (m.acc = a))))                                   
<1> SUFFICES ASSUME NEW  P \in Proposers,
                        HighestProposer(P)
                      /\(\E t \in Time : state_time = t
                      /\ \E b \in Ballots : 
                           (\E Q \in Quorums : 
                             \A a \in Q : \E m \in msgs : (m.type = "1b") 
                                                       /\ (m.bal = b)  
                                                       /\ (m.prop = P) 
                                                       /\ (m.acc = a))
                        /\ \E v \in Values : (\E m \in msgs : (m.type = "2a") 
                                                           /\ (m.prop = P) 
                                                           /\ (m.bal = b) 
                                                           /\ (m.val = v)))
                      /\ Assumptions
             PROVE    (\E t \in Time : state_time' = t 
                                    /\ \E v \in Values : 
                                       (\E Q \in Quorums : 
                                         \A a \in Q : 
                                         (\E m \in msgs' : (m.type = "2b") 
                                                        /\ (m.val = v) 
                                                        /\ (m.acc = a))))
    OBVIOUS
<1>1. HighestProposerAssertion2
    BY DEF Assumptions, HighestAssertions    
<1>2. HighestProposer(P) 
     /\ (\E b \in Ballots : 
         (\E Q \in Quorums : 
           \A a \in Q : \E m \in msgs : (m.type = "1b") 
                                     /\ (m.bal = b)  /\ (m.prop = P) /\ (m.acc = a))
                                     /\ \E v \in Values : 
                                        (\E m \in msgs : (m.type = "2a") 
                                                      /\ (m.prop = P) 
                                                      /\ (m.bal = b) 
                                                      /\ (m.val = v)))
    OBVIOUS
<1>3.  HighestProposer(P) 
       /\ \E b \in Ballots : 
          (\E Q \in Quorums : \A a \in Q : \E m \in msgs : (m.type = "1b") 
                                                        /\ (m.bal = b)  
                                                        /\ (m.prop = P) 
                                                        /\ (m.acc = a))
                                         /\ \E v \in Values : 
                                            (\E m \in msgs : (m.type = "2a") 
                                                          /\ (m.prop = P) 
                                                          /\ (m.bal = b) 
                                                          /\ (m.val = v)
                                         /\  (\A a \in Acceptors : 
                                               \E m1 \in msgs : m1.type = "2a" 
                                                             /\ m1.prop = P 
                                                             /\ maxBal[a]<=m1.bal) )
    BY <1>2, <1>1 DEF HighestProposerAssertion2
<1>4. aPropLimit /\ aTypeOk
    BY DEF Assumptions
<1>5. HighestProposer(P) 
       /\ \E b \in Ballots : 
          (\E Q \in Quorums : \A a \in Q : 
                                \E m \in msgs : (m.type = "1b") /\ (m.bal = b)  
                                             /\ (m.prop = P) /\ (m.acc = a))
                                 /\ \E v \in Values : (\E m \in msgs : (m.type = "2a") 
                                                                    /\ (m.prop = P) 
                                                                    /\ (m.bal = b) 
                                                                    /\ (m.val = v)
                                 /\  (\A a \in Acceptors : 
                                       \E m1 \in msgs : m1.type = "2a" 
                                                     /\ m1.prop = P 
                                                     /\ maxBal[a]<=b ))
    BY <1>3, <1>4 DEF aPropLimit
<1>6. \E b \in Ballots : 
      (\E Q \in Quorums : \A a \in Q : 
        \E m \in msgs : (m.type = "1b") /\ (m.bal = b)  /\ (m.prop = P) /\ (m.acc = a))
                 /\ \E v \in Values : 
                     (\E m \in msgs : (m.type = "2a") /\ (m.prop = P) 
                                   /\ (m.bal = b) /\ (m.val = v) 
                 /\  (\A Q \in Quorums : \A a \in Q :  maxBal[a]<=b ))
    BY <1>5, <1>4 DEF aTypeOk                                                                                                        
<1>200. QED
    BY <1>6, Lemma3       


----------------------------------------------------------------------------
(***************************************************************************)
(*The intermediate states                                                  *)
(***************************************************************************)
\* after a proposer has sent 1a msgs and has not received 1b messages yet
msgsPost1a(P) ==
( \E b \in Ballots : (\E m \in msgs : m.type = "1a" /\ m.prop = P /\ m.bal = b)
               /\ (~(\E m2 \in msgs: m2.type = "1b" /\ m2.prop = P))
               /\ (~(\E m2 \in msgs: m2.type = "2a" /\ m2.prop = P))
               /\ (~(\E m2 \in msgs: m2.type = "2b" /\ m2.prop = P)))

\* after a proposer has sent 1a msgs and has received 1b messages 
msgsPost1b(P) ==
(    (\E b \in Ballots : 
       \E Q \in Quorums : 
        \A a \in Q : 
         (\E m \in msgs : 
           (m.type = "1b") /\ (m.prop = P) /\ (m.acc = a) /\ (m.bal = b))))

\* after a proposer has sent 2a msgs
msgsPost2a(P) ==
(\E b \in Ballots :  
 (\E Q \in Quorums : 
   \A a \in Q : \E m \in msgs : (m.type = "1b") /\ (m.bal = b)  
                             /\ (m.prop = P) /\ (m.acc = a)) 
/\ \E v \in Values : (\E m \in msgs : m.type = "2a" /\ m.prop = P 
                                   /\ m.bal = b /\ m.val = v))

\* after a proposer has received 2b messages from a quorum
msgsPost2b(v) ==
(\E Q \in Quorums : \A a \in Q : (\E m \in msgs : (m.type = "2b") 
                                               /\ (m.val = v) 
                                               /\ (m.acc = a)))
----------------------------------------------------------------------------
(***************************************************************************)
(*The main proof of progress                                               *)
(***************************************************************************)
\* Eventually_1a_from_highest
LEMMA Lemma6 ==
Assumptions =>
 \E P \in Proposers:
          HighestProposer(P)
       /\ \E t \in Time : state_time = t /\ msgsPost1a(P) 
<1> SUFFICES ASSUME Assumptions
             PROVE        
                     \E P \in Proposers:
                              HighestProposer(P)
                           /\ \E t \in Time : state_time = t /\ msgsPost1a(P)                                       
    OBVIOUS
<1>1. TemporalProperty2 /\ TemporalProperty3
    BY DEF Assumptions, aTypeOk, TemporalProperties
<1>2.  HighestAssertions /\ aAvailability
    BY DEF Assumptions 
<1>3. \E P \in Proposers : HighestProposer(P)
    BY <1>2 DEF HighestAssertions 
<1>4. \E P \in Proposers : HighestProposer(P) /\ Always_available(P)
    BY <1>3, <1>2 DEF aAvailability, Highest_prop_always_available 
<1>5. \E P \in Proposers : HighestProposer(P) 
                        /\ Always_available(P)
                        /\ (\E t \in Time :   state_time = t
                                           /\ (~(\E m \in msgs : m.prop = P)))
    BY <1>4, <1>1 DEF TemporalProperty2
<1>5a. \E P \in Proposers : HighestProposer(P) 
                        /\ Always_available(P)
                        /\ (\E t \in Time :   state_time = t
                                           /\ Available(P,t) 
                                           /\ (~(\E m \in msgs : m.prop = P)))
    BY <1>5 DEF Always_available    
<1>5c. \E P \in Proposers : 
       HighestProposer(P) 
    /\ Always_available(P) 
    /\ (\E t2 \in Time : state_time' = t2 
                    /\ \E b \in Ballots : 
                        (\E m \in msgs' : m.type = "1a" /\ m.prop = P /\ m.bal = b)
                   /\ (~(\E m2 \in msgs': m2.type = "1b" /\ m2.prop = P))
                   /\ (~(\E m2 \in msgs': m2.type = "2a" /\ m2.prop = P))
                               /\ (~(\E m2 \in msgs': m2.type = "2b" /\ m2.prop = P)) )                                                      
    BY <1>5a, Lemma1
<1>6. \E P \in Proposers : 
       HighestProposer(P) 
    /\ Always_available(P) 
    /\ (\E t2 \in Time : state_time = t2 
                    /\ \E b \in Ballots : 
                        (\E m \in msgs : m.type = "1a" /\ m.prop = P /\ m.bal = b)
                   /\ (~(\E m2 \in msgs: m2.type = "1b" /\ m2.prop = P))
                   /\ (~(\E m2 \in msgs: m2.type = "2a" /\ m2.prop = P))
                               /\ (~(\E m2 \in msgs: m2.type = "2b" /\ m2.prop = P)) )
    BY <1>5c, <1>1 DEF TemporalProperty3
<1>7. (\E P \in Proposers : HighestProposer(P) /\ \E t \in Time : state_time = t /\ msgsPost1a(P))
    BY <1>6 DEF msgsPost1a                                                                                                                        
<1>200. QED
    BY <1>7                           

\* Eventually_1b_to_highest_from_quorum                                 
LEMMA Lemma7 ==
Assumptions
=> 
 \E P \in Proposers : 
          HighestProposer(P)  
       /\ \E t \in Time : state_time = t /\ msgsPost1b(P)
<1> SUFFICES ASSUME Assumptions
             PROVE                             
                     \E P \in Proposers : 
                              HighestProposer(P)  
                           /\ \E t \in Time : state_time = t /\ msgsPost1b(P)
             OBVIOUS
<1>1. (\E P \in Proposers :
                     HighestProposer(P) 
                   /\ \E t \in Time : state_time = t /\ msgsPost1a(P) )                                                  
     BY Lemma6
<1>2. \E P \in Proposers :
         HighestProposer(P)                   
       /\ (\E t \in Time : state_time = t 
                        /\ \E b \in Ballots : 
                           (\E m \in msgs : m.type = "1a" /\ m.prop = P /\ m.bal = b)
                    /\ (~(\E m2 \in msgs: m2.type = "1b" /\ m2.prop = P)))
     BY <1>1 DEF msgsPost1a
<1>2a.  HighestAssertions /\ aAvailability /\ TemporalProperties
    BY DEF Assumptions, aTypeOk         
<1>3.  \E P \in Proposers :
         HighestProposer(P)                   
       /\ Always_available(P)   
       /\ (\E t \in Time : state_time = t 
                        /\ \E b \in Ballots : 
                           (\E m \in msgs : m.type = "1a" /\ m.prop = P /\ m.bal = b)
                    /\ (~(\E m2 \in msgs: m2.type = "1b" /\ m2.prop = P)))      
    BY <1>2, <1>2a DEF aAvailability,  Highest_prop_always_available  
<1>4.  \E P \in Proposers :
         HighestProposer(P)                   
       /\ Always_available(P)   
       /\ (\E t \in Time : state_time = t 
                        /\ Available(P,t) 
                        /\ \E b \in Ballots : 
                        (\E m \in msgs : m.type = "1a" /\ m.prop = P /\ m.bal = b)
                    /\ (~(\E m2 \in msgs: m2.type = "1b" /\ m2.prop = P)))      
    BY <1>3 DEF Always_available     
<1>20.   (\E P \in Proposers : HighestProposer(P)  
            /\ (\E t \in Time : state_time' = t 
               /\ (\E b \in Ballots : 
                   \E Q \in Quorums : 
                    \A a \in Q : 
                     (\E m \in msgs' : 
                       (m.type = "1b") /\ (m.prop = P) /\ (m.acc = a) /\ (m.bal = b)))))
     BY <1>4, Lemma4
<1>21. TemporalProperty3
     BY <1>2a DEF TemporalProperties
<1>22.\A t \in Time:  \A P \in Proposers: 
         ((state_time' = t 
           /\ (\E b \in Ballots : 
               \E Q \in Quorums : 
                \A a \in Q : 
                 (\E m \in msgs' : 
                   (m.type = "1b") /\ (m.prop = P) /\ (m.acc = a) /\ (m.bal = b)))))
        =>
          (\E t2 \in Time:
                 (t2>t
               /\ state_time = t2  
               /\ (\E b \in Ballots : 
                   \E Q \in Quorums : 
                    \A a \in Q : 
                     (\E m \in msgs : 
                       (m.type = "1b") /\ (m.prop = P) /\ (m.acc = a) /\ (m.bal = b)))))
     BY <1>21 DEF TemporalProperty3 
<1>23.    (\E P \in Proposers : HighestProposer(P)  
            /\ (\E t \in Time : state_time = t 
               /\ (\E b \in Ballots : 
                   \E Q \in Quorums : 
                    \A a \in Q : 
                     (\E m \in msgs : (m.type = "1b") /\ (m.prop = P) 
                                   /\ (m.acc = a) /\ (m.bal = b)))))
     BY <1>20, <1>22 
<1>24. \E P \in Proposers : 
                  HighestProposer(P)  
               /\ \E t \in Time : state_time = t /\ msgsPost1b(P)                                                                          
     BY <1>23 DEF msgsPost1b
<1>200. QED
    BY <1>24

\* Eventually_2a_from_highest
LEMMA  Lemma8 ==
Assumptions
=>
(
 (\E P \in Proposers : HighestProposer(P)  
                       /\  (\E t2 \in Time : state_time = t2 /\ msgsPost2a(P)))
)
<1> SUFFICES ASSUME Assumptions 
             PROVE
                (\E P \in Proposers : HighestProposer(P)  
                       /\  (\E t2 \in Time : state_time = t2 /\ msgsPost2a(P)))
    OBVIOUS
<1>1. \E P \in Proposers : HighestProposer(P)
                  /\ (\E t \in Time : state_time = t 
                       /\ (\E b \in Ballots : 
                           \E Q \in Quorums : 
                            \A a \in Q : 
                             (\E m \in msgs : 
                               (m.type = "1b") /\ (m.prop = P) /\ (m.acc = a) /\ (m.bal = b))))
    BY Lemma7 DEF msgsPost1b 
<1>2.  HighestAssertions /\ aAvailability /\TemporalProperties
    BY DEF Assumptions, aTypeOk  
<1>3. \E P \in Proposers : HighestProposer(P)
                  /\ Always_available(P)
                  /\ (\E t \in Time : state_time = t 
                       /\ (\E b \in Ballots : 
                           \E Q \in Quorums : 
                            \A a \in Q : 
                             (\E m \in msgs : 
                               (m.type = "1b") /\ (m.prop = P) /\ (m.acc = a) /\ (m.bal = b))))
    BY <1>1, <1>2 DEF aAvailability,  Highest_prop_always_available   
<1>4. \E P \in Proposers : HighestProposer(P)
                  /\ (\E t \in Time : state_time = t 
                       /\ Available(P,t)
                       /\ (\E b \in Ballots : 
                           \E Q \in Quorums : 
                            \A a \in Q : 
                             (\E m \in msgs : 
                                           (m.type = "1b") /\ (m.prop = P) 
                                        /\ (m.acc = a) /\ (m.bal = b))))
    BY <1>3 DEF Always_available     
<1>5.(\E P \in Proposers : 
        HighestProposer(P)  
   /\  (\E t2 \in Time : state_time' = t2 
                      /\ \E b \in Ballots :  
                         (\E Q \in Quorums : 
                           \A a \in Q : \E m \in msgs' : (m.type = "1b") 
                                                      /\ (m.bal = b)  
                                                      /\ (m.prop = P) 
                                                      /\ (m.acc = a)) 
                      /\ \E v \in Values : (\E m \in msgs' : m.type = "2a" 
                                                          /\ m.prop = P 
                                                          /\ m.bal = b 
                                                          /\ m.val = v)) ) 
    BY <1>4, Lemma2
<1>6.\A t \in Time:
     \A P \in Proposers:   
         ((state_time' = t 
           /\ \E b \in Ballots :  (\E Q \in Quorums : 
                                    \A a \in Q : \E m \in msgs' : (m.type = "1b") 
                                                               /\ (m.bal = b)  
                                                               /\ (m.prop = P) 
                                                               /\ (m.acc = a)) 
                                     /\ \E v \in Values : 
                                        (\E m \in msgs' : m.type = "2a" 
                                                       /\ m.prop = P 
                                                       /\ m.bal = b 
                                                       /\ m.val = v)))
        =>
          (\E t2 \in Time:
                 (t2>t
               /\ state_time = t2  
               /\ \E b \in Ballots :  
                   (\E Q \in Quorums : 
                     \A a \in Q : \E m \in msgs : (m.type = "1b") /\ (m.bal = b)  
                                               /\ (m.prop = P) /\ (m.acc = a)) 
                 /\ \E v \in Values : (\E m \in msgs : m.type = "2a" 
                                                    /\ m.prop = P 
                                                    /\ m.bal = b 
                                                    /\ m.val = v))) 
    BY <1>2 DEF TemporalProperties, TemporalProperty3
<1>7. (\E P \in Proposers : 
       HighestProposer(P)  
   /\  (\E t2 \in Time : state_time = t2 
     /\ \E b \in Ballots :  (\E Q \in Quorums : 
                              \A a \in Q : 
                               \E m \in msgs : (m.type = "1b") /\ (m.bal = b)  
                                            /\ (m.prop = P) /\ (m.acc = a)) 
                         /\ \E v \in Values : 
                            (\E m \in msgs : m.type = "2a" /\ m.prop = P 
                                          /\ m.bal = b /\ m.val = v)) ) 
    BY <1>5, <1>6 
<1>8.(\E P \in Proposers : HighestProposer(P)  
                       /\  (\E t2 \in Time : state_time = t2 /\ msgsPost2a(P)))                                          
    BY <1>7 DEF msgsPost2a                                                                                                                     
<1>200. QED
     BY <1>8

\* Eventually_2b_to_highest_from_quorum
LEMMA  Lemma9 ==
Assumptions
=>
(
    ((\E t \in Time : state_time = t /\  \E v \in Values : msgsPost2b(v))) 
)
<1> SUFFICES ASSUME Assumptions,  (\E P \in Proposers : HighestProposer(P) 
                                                     /\ \E t \in Time : state_time = t 
                                                                     /\ msgsPost2a(P))
             PROVE
                    ((\E t \in Time : state_time = t /\  \E v \in Values : msgsPost2b(v)))              
    BY Lemma8 DEF msgsPost2a
<1>1. (\E P \in Proposers :
            HighestProposer(P)   
         /\ (\E t2 \in Time : state_time = t2 
            /\ \E b \in Ballots :  
               (\E Q \in Quorums : 
                 \A a \in Q : \E m \in msgs : (m.type = "1b") /\ (m.bal = b)  
                                           /\ (m.prop = P) /\ (m.acc = a)) 
           /\ \E v \in Values : (\E m \in msgs : m.type = "2a" /\ m.prop = P 
                                              /\ m.bal = b /\ m.val = v)))
    BY DEF msgsPost2a
<1>2.  HighestAssertions /\ aAvailability /\TemporalProperties
    BY DEF Assumptions, aTypeOk  
<1>3. (\E P \in Proposers :
            HighestProposer(P) 
         /\ Always_available(P)     
         /\ (\E t2 \in Time : state_time = t2 
            /\ \E b \in Ballots :  
               (\E Q \in Quorums : 
                 \A a \in Q : \E m \in msgs : (m.type = "1b") /\ (m.bal = b)  
                                           /\ (m.prop = P) /\ (m.acc = a)) 
           /\ \E v \in Values : (\E m \in msgs : m.type = "2a" /\ m.prop = P 
                                              /\ m.bal = b /\ m.val = v)))  
    BY <1>1, <1>2 DEF aAvailability,  Highest_prop_always_available 
<1>4. (\E P \in Proposers :
            HighestProposer(P) 
         /\ Always_available(P)     
         /\ (\E t2 \in Time : state_time = t2 
            /\ Available(P,t2)
            /\ \E b \in Ballots :  
               (\E Q \in Quorums : 
                 \A a \in Q : 
                  \E m \in msgs : (m.type = "1b") /\ (m.bal = b)  
                               /\ (m.prop = P) /\ (m.acc = a)) 
             /\ \E v \in Values : (\E m \in msgs : m.type = "2a" /\ m.prop = P 
                                                /\ m.bal = b /\ m.val = v)))  
    BY <1>3 DEF Always_available  
<1>5.(\E P \in Proposers :
         HighestProposer(P)
      /\ (\E t \in Time : state_time' = t 
                       /\ \E v \in Values : 
                          (\E Q \in Quorums : 
                            \A a \in Q : 
                             (\E m \in msgs' : (m.type = "2b") 
                                            /\ (m.val = v) 
                                            /\ (m.acc = a)))))                                                      
    BY <1>4, Lemma5
<1>6.\A t \in Time:   
         ((state_time' = t 
           /\ \E v \in Values : 
              (\E Q \in Quorums : 
                \A a \in Q : 
                 (\E m \in msgs' : (m.type = "2b") 
                                /\ (m.val = v) 
                                /\ (m.acc = a)))))
        =>
          (\E t2 \in Time:
                 (t2>t
               /\ state_time = t2  
               /\ \E v \in Values : 
                  (\E Q \in Quorums : 
                    \A a \in Q : 
                     (\E m \in msgs : (m.type = "2b") 
                                   /\ (m.val = v) 
                                   /\ (m.acc = a)))))     
    BY <1>2 DEF TemporalProperties, TemporalProperty3
<1>7. (\E P \in Proposers :
       HighestProposer(P)
      /\ (\E t \in Time : state_time = t 
                      /\ \E v \in Values : 
                         (\E Q \in Quorums : 
                           \A a \in Q : 
                            (\E m \in msgs : (m.type = "2b") 
                                          /\ (m.val = v) 
                                          /\ (m.acc = a)))))    
    BY <1>5, <1>6 
<1>8.(\E P \in Proposers :
               HighestProposer(P)
              /\ (\E t \in Time : state_time = t  
                              /\  \E v \in Values : msgsPost2b(v)))       
    BY <1>7 DEF msgsPost2b
<1>200. QED
   BY <1>8


LEMMA Theorem1 ==
Assumptions 
=>
(
(\E v \in Values : \E l \in Learners : \E t \in Time : 
                                          learnt' = [learnt EXCEPT ![l] = v])
)
<1> SUFFICES ASSUME Assumptions
             PROVE (\E t \in Time : \E v \in Values : \E l \in Learners : 
                                          learnt' = [learnt EXCEPT ![l] = v])
    OBVIOUS    
<1>1. \E v \in Values : \E Q \in Quorums : 
                \A a \in Q : (\E m \in msgs : (m.type = "2b") 
                                           /\ (m.val = v) 
                                           /\ (m.acc = a)) 
   BY Lemma9 DEF msgsPost2b
<1>2. \E l \in Learners : Always_available(l)
   BY DEF Assumptions, aAvailability, Learner_always_available
<1>3. \E l \in Learners : Rule_learner(l)
   BY <1>2 DEF Assumptions, aBehavior, Learner_behaviour       
<1>4. \E v \in Values : \E l \in Learners : \E t \in Time : Learning(l,v,t)
   BY <1>1, <1>3 DEF Rule_learner  
<1>5. (\E v \in Values : \E l \in Learners : \E t \in Time : 
                                          learnt' = [learnt EXCEPT ![l] = v])
   BY <1>4 DEF Learning        
<1>200. QED
   BY <1>5  


=============================================================================
\* Modification History
\* Last modified Sun Apr 12 13:32:37 EDT 2020 by pauls
\* Created Thu Nov 14 15:15:40 EST 2019 by pauls
