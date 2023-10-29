------------------------------ MODULE MQTTclasse3QoS2 ---------------------------

EXTENDS  Sequences,Naturals,TLC,FiniteSets

CONSTANTS any

VARIABLES depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack, _pc

vars == << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack, _pc >>

upperbound(S) == CHOOSE n \in S : 
            /\ \A m \in S : n >= m

lowerbound(S) == CHOOSE n \in S : 
            /\ \A m \in S : m >= n

Broker == 
          LET Broker_start == 1 IN 
           LET Broker_end == 1 IN
               Broker_start .. Broker_end

attaque == 
           LET attaque_start == upperbound(Broker) + 1 IN 
            LET attaque_end == upperbound(Broker) + 1 IN
                attaque_start .. attaque_end

Publisher == 
             LET Publisher_start == upperbound(attaque) + 1 IN 
              LET Publisher_end == upperbound(attaque) + 1 IN
                  Publisher_start .. Publisher_end

ProcSet == Broker \cup attaque \cup Publisher

send(ch,msg) == [network EXCEPT ![ch] = Append(@, msg)]

Init == 
    /\ depth = 0
    /\ cp = any
    /\ network = [p \in (Broker \cup Publisher) |-> <<>>]
    /\ activeClients = {}
    /\ Topics = {"A", "B", "C"}
    /\ TopicPool = [t \in Topics |-> {}]
    /\ _Broker_data = [self \in Broker |-> [ self |-> self, parentID |-> 0, Name|->"Broker", rules|->0, status|->0, statusRecord|->0, wait_REL|->{}]]

    /\ _attaque_data = [self \in attaque |-> [ self |-> self, parentID |-> 0, Name|->"attaque", BrokerID|->1, INJ1|->FALSE, INJ2|->FALSE, INJ3|->FALSE]]

    /\ _Publisher_data = [self \in Publisher |-> [ self |-> self, parentID |-> 0, Name|->"Publisher", CONNSUCC|->FALSE, PUBSUCC|->FALSE, BrokerID|->1]]

    /\ _stack = [self \in ProcSet |-> << >>]
    /\ _pc = [self \in ProcSet |-> CASE self \in Broker -> "listen"
                         []self \in attaque -> "Lbl_7"
                         []self \in Publisher -> "PubStart"]

Push(s,e) == e \circ s 

Lbl_1(self) == 
               /\ _pc[self] = "Lbl_1"
               /\ (cp = any \/ cp = self)
               /\ \/ /\ (({Head(_stack[self]).pkt.sender} \cap activeClients) # {})
                        /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBCOMP", sender |-> self]) IN
                           /\ network' = _network
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                  \/ /\ ~((({Head(_stack[self]).pkt.sender} \cap activeClients) # {}))
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
Lbl_2(self) == 
               /\ _pc[self] = "Lbl_2"
               /\ (cp = any \/ cp = self)
               /\ \/ /\ (({Head(_stack[self]).pkt.sender} \cap activeClients) # {})
                        /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBREL", sender |-> self]) IN
                           /\ network' = _network
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                  \/ /\ ~((({Head(_stack[self]).pkt.sender} \cap activeClients) # {}))
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
Lbl_3(self) == 
               /\ _pc[self] = "Lbl_3"
               /\ (cp = any \/ cp = self)
               /\ \/ /\ (({Head(_stack[self]).pkt.sender} \cap activeClients) # {})
                        /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PINGRESP", sender |-> self]) IN
                           /\ network' = _network
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                  \/ /\ ~((({Head(_stack[self]).pkt.sender} \cap activeClients) # {}))
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
cqos2(self) == 
               /\ _pc[self] = "cqos2"
               /\ (cp = any \/ cp = self)
               /\ LET _network == send(Head(_stack[self]).to, [type |-> "PUBLISH", sender |-> self, topic |-> "A", QoS |-> 2]) IN
                  /\ network' = _network
                  /\ _pc' = [_pc EXCEPT ![self] = "waitPUB2"]
                  /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
waitPUB2(self) == 
                  /\ _pc[self] = "waitPUB2"
                  /\ (cp = any \/ cp = self)
                  /\ \/ /\ (Len(network[self]) > 0)
                           /\ LET packet == Head(network[self]) IN
                              \/ /\ (packet.type = "PUBREC")
                                    /\ LET _network == send(Head(_stack[self]).to, [type |-> "PUBREL", sender |-> self, topic |-> "A", QoS |-> 2]) IN
                                       LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                       /\ network' = __network
                                       /\ _pc' = [_pc EXCEPT ![self] = "waitPUBCOMP2"]
                                       /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                              \/ /\ ~((packet.type = "PUBREC"))
                                    /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                       /\ network' = _network
                                       /\ _pc' = [_pc EXCEPT ![self] = "waitPUBCOMP2"]
                                       /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
waitPUBCOMP2(self) == 
                      /\ _pc[self] = "waitPUBCOMP2"
                      /\ (cp = any \/ cp = self)
                      /\ \/ /\ (Len(network[self]) > 0)
                               /\ LET pkt == Head(network[self]) IN
                                  \/ /\ (pkt.type = "PUBCOMP")
                                        /\ LET _newhead == Head(_stack[self]) IN
                                           LET __newhead == [_newhead EXCEPT !.PUBSUCC = TRUE ] IN
                                           LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                           LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<__newhead>>) ] IN
                                           LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                           \/ /\ (Head(___stack[self]).PUBSUCC = TRUE)
                                                    /\ _stack' = ___stack
                                                    /\ network' = _network
                                                    /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                    /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data >>
                                           \/ /\ ~((Head(___stack[self]).PUBSUCC = TRUE))
                                                    /\ _stack' = ___stack
                                                    /\ network' = _network
                                                    /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                    /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data >>
                                  \/ /\ ~((pkt.type = "PUBCOMP"))
                                        /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                           \/ /\ (Head(_stack[self]).PUBSUCC = TRUE)
                                                    /\ network' = _network
                                                    /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                    /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                                           \/ /\ ~((Head(_stack[self]).PUBSUCC = TRUE))
                                                    /\ network' = _network
                                                    /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                    /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
rqos2(self) == 
               /\ _pc[self] = "rqos2"
               /\ (cp = any \/ cp = self)
               /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBREC", sender |-> self]) IN
                  /\ network' = _network
                  /\ _pc' = [_pc EXCEPT ![self] = "waitPUBREL"]
                  /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
waitPUBREL(self) == 
                    /\ _pc[self] = "waitPUBREL"
                    /\ (cp = any \/ cp = self)
                    /\ \/ /\ (Len(network[self]) > 0)
                             /\ LET packet == Head(network[self]) IN
                                \/ /\ (packet.type = "PUBREL")
                                      /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBCOMP", sender |-> self]) IN
                                         LET _newhead == Head(_stack[self]) IN
                                         LET __newhead == [_newhead EXCEPT !.PUBSUCC = TRUE ] IN
                                         LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                         LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<__newhead>>) ] IN
                                         LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                         \/ /\ (Head(___stack[self]).PUBSUCC = TRUE)
                                                  /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                  /\ network' = __network
                                                  /\ _stack' = ___stack
                                                  /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data >>
                                         \/ /\ ~((Head(___stack[self]).PUBSUCC = TRUE))
                                                  /\ _stack' = ___stack
                                                  /\ network' = __network
                                                  /\ _pc' = [_pc EXCEPT ![self] = "rqos2"]
                                                  /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data >>
                                \/ /\ ~((packet.type = "PUBREL"))
                                      /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                         \/ /\ (Head(_stack[self]).PUBSUCC = TRUE)
                                                  /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                  /\ network' = _network
                                                  /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                                         \/ /\ ~((Head(_stack[self]).PUBSUCC = TRUE))
                                                  /\ network' = _network
                                                  /\ _pc' = [_pc EXCEPT ![self] = "rqos2"]
                                                  /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
l1(self) == 
            /\ _pc[self] = "l1"
            /\ (cp = any \/ cp = self)
            /\ \/ /\ (Head(_stack[self]).pkt.QoS = 0)
                     /\ \/ /\ (TopicPool[Head(_stack[self]).pkt.topic] # {})
                                 /\ _pc' = [_pc EXCEPT ![self] = "Lbl_4"]
                                 /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                        \/ /\ ~((TopicPool[Head(_stack[self]).pkt.topic] # {}))
                                 /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                 /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
               \/ /\ (Head(_stack[self]).pkt.QoS = 1)
                        /\ _pc' = [_pc EXCEPT ![self] = "Lbl_5"]
                        /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
               \/ /\ (Head(_stack[self]).pkt.QoS = 2)
                     /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBREC", sender |-> self]) IN
                        LET __Broker_data == [_Broker_data EXCEPT ![self].wait_REL = (_Broker_data[self].wait_REL \cup {Head(_stack[self]).pkt.sender})] IN
                        /\ network' = _network
                        /\ _Broker_data' = __Broker_data
                        /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                        /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _attaque_data, _Publisher_data, _stack >>
Lbl_4(self) == 
               /\ _pc[self] = "Lbl_4"
               /\ (cp = any \/ cp = self)
               /\ IF TopicPool[Head(_stack[self]).pkt.topic] # {} /\ Head(_stack[self]).idS_sub = {}
                        THEN /\ LET newHead1 == Head(_stack[self]) IN
                                LET _newHead1 == [newHead1 EXCEPT !.idS_sub = TopicPool[Head(_stack[self]).pkt.topic] ] IN
                                LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead1>>) ] IN
                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_4"]
                                /\ _stack' = ___stack
                                /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data >>
                        ELSE
                             /\ IF Head(_stack[self]).idS_sub # {}
                                      THEN /\ LET sub == CHOOSE fech \in Head(_stack[self]).idS_sub : TRUE IN
                                              LET newHead2 == Head(_stack[self]) IN
                                              LET _newHead2 == [newHead2 EXCEPT !.sub = sub ] IN
                                              LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                              LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead2>>) ] IN
                                              LET _network == send(Head(___stack[self]).sub, [type |-> "PUBLISH", sender |-> self, QoS |-> 0]) IN
                                              LET __newhead == Head(___stack[self]) IN
                                              LET ___newhead == [__newhead EXCEPT !.idS_sub = Head(___stack[self]).idS_sub \ {Head(___stack[self]).sub } ] IN
                                              LET ____stack == [___stack EXCEPT ![self] = Tail(___stack[self]) ] IN
                                              LET _____stack == [____stack EXCEPT ![self] = Push(____stack[self], <<___newhead>>) ] IN
                                              /\ IF Head(_____stack[self]).idS_sub # {}
                                                    THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_4"]
                                                            /\ _stack' = _____stack
                                                            /\ network' = _network
                                                            /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data >>
                                                    ELSE
                                                            /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                            /\ _stack' = _____stack
                                                            /\ network' = _network
                                                            /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data >>
                                      ELSE
                                              /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                              /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
Lbl_5(self) == 
               /\ _pc[self] = "Lbl_5"
               /\ (cp = any \/ cp = self)
               /\ IF TopicPool[Head(_stack[self]).pkt.topic] # {} /\ Head(_stack[self]).idS_sub = {}
                        THEN /\ LET newHead3 == Head(_stack[self]) IN
                                LET _newHead3 == [newHead3 EXCEPT !.idS_sub = TopicPool[Head(_stack[self]).pkt.topic] ] IN
                                LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead3>>) ] IN
                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_5"]
                                /\ _stack' = ___stack
                                /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data >>
                        ELSE
                             /\ IF Head(_stack[self]).idS_sub # {}
                                      THEN /\ LET sub == CHOOSE fech \in Head(_stack[self]).idS_sub : TRUE IN
                                              LET newHead4 == Head(_stack[self]) IN
                                              LET _newHead4 == [newHead4 EXCEPT !.sub = sub ] IN
                                              LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                              LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead4>>) ] IN
                                              LET _network == send(Head(___stack[self]).sub, [type |-> "PUBLISH", sender |-> self, QoS |-> 1]) IN
                                              LET __newhead == Head(___stack[self]) IN
                                              LET ___newhead == [__newhead EXCEPT !.idS_sub = Head(___stack[self]).idS_sub \ {Head(___stack[self]).sub } ] IN
                                              LET ____stack == [___stack EXCEPT ![self] = Tail(___stack[self]) ] IN
                                              LET _____stack == [____stack EXCEPT ![self] = Push(____stack[self], <<___newhead>>) ] IN
                                              /\ IF Head(_____stack[self]).idS_sub # {}
                                                    THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_5"]
                                                            /\ _stack' = _____stack
                                                            /\ network' = _network
                                                            /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data >>
                                                    ELSE
                                                         /\ LET __network == send(Head(_____stack[self]).pkt.sender, [type |-> "PUBACK", sender |-> self]) IN
                                                            /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                            /\ _stack' = _____stack
                                                            /\ network' = __network
                                                            /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data >>
                                      ELSE
                                           /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBACK", sender |-> self]) IN
                                              /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                              /\ network' = _network
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
listen(self) == 
                /\ _pc[self] = "listen"
                /\ cp = any
                /\ \/ /\ (Len(network[self]) > 0)
                         /\ LET packet == Head(network[self]) IN
                            \/ /\ (packet.type = "CONNECT")
                                  /\ LET _activeClients == (activeClients \cup {packet.sender}) IN
                                     LET _network == send(packet.sender, [type |-> "CONNACK", sender |-> self]) IN
                                     LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                     /\ activeClients' = _activeClients
                                     /\ network' = __network
                                     /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                     /\ UNCHANGED << depth, cp, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                            \/ /\ (packet.type = "PUBLISH")
                                  /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                     LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, sub|->0, idS_sub|->{}, _pc |->"listen"]>>)] IN
                                     /\ _pc' = [_pc EXCEPT ![self] = "l1"]
                                     /\ network' = _network
                                     /\ _stack' = __stack
                                     /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data >>
                            \/ /\ (packet.type = "PUBACK")
                                  /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                     /\ network' = _network
                                     /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                     /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                            \/ /\ (packet.type = "PUBREL")
                                  /\ \/ /\ (({packet.sender} \cap _Broker_data[self].wait_REL) # {})
                                           /\ LET __Broker_data == [_Broker_data EXCEPT ![self].wait_REL = (_Broker_data[self].wait_REL \ {packet.sender})] IN
                                              LET _network == send(packet.sender, [type |-> "PUBCOMP", sender |-> self]) IN
                                              LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                              /\ _Broker_data' = __Broker_data
                                              /\ network' = __network
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _attaque_data, _Publisher_data, _stack >>
                                     \/ /\ ~((({packet.sender} \cap _Broker_data[self].wait_REL) # {}))
                                           /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                              /\ network' = _network
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                            \/ /\ (packet.type = "SUBSCRIBE")
                                  /\ \/ /\ (({packet.sender} \cap activeClients) # {})
                                           /\ LET _TopicPool == [TopicPool EXCEPT ![packet.topic] = (TopicPool[packet.topic] \cup {packet.sender})] IN
                                              LET _network == send(packet.sender, [type |-> "SUBACK", sender |-> self]) IN
                                              LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                              /\ TopicPool' = _TopicPool
                                              /\ network' = __network
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                                     \/ /\ ~((({packet.sender} \cap activeClients) # {}))
                                           /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                              /\ network' = _network
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                            \/ /\ (packet.type = "UNSUBSCRIBE")
                                  /\ \/ /\ (({packet.sender} \cap activeClients) # {})
                                           /\ LET _TopicPool == [TopicPool EXCEPT ![packet.topic] = (TopicPool[packet.topic] \ {packet.sender})] IN
                                              LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                              /\ TopicPool' = _TopicPool
                                              /\ network' = _network
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                                     \/ /\ ~((({packet.sender} \cap activeClients) # {}))
                                           /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                              /\ network' = _network
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                            \/ /\ (packet.type = "PINGREQ")
                                  /\ LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, _pc |->"Lbl_6"]>>)] IN
                                     /\ _pc' = [_pc EXCEPT ![self] = "Lbl_3"]
                                     /\ _stack' = __stack
                                     /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data >>
                            \/ /\ (packet.type = "DISCONNECT")
                                  /\ LET _activeClients == (activeClients \ {packet.sender}) IN
                                     LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                     /\ activeClients' = _activeClients
                                     /\ network' = _network
                                     /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                     /\ UNCHANGED << depth, cp, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                   \/ /\ ~((Len(network[self]) > 0))
                            /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                            /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
Lbl_6(self) == 
               /\ _pc[self] = "Lbl_6"
               /\ cp = any
               /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                  /\ network' = _network
                  /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                  /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
_Broker(self) == 
                     listen(self) \/ Lbl_6(self) \/ Lbl_1(self) \/ Lbl_2(self) \/ Lbl_3(self) \/ cqos2(self) \/ waitPUB2(self) \/ waitPUBCOMP2(self) \/ rqos2(self) \/ waitPUBREL(self) \/ l1(self) \/ Lbl_4(self) \/ Lbl_5(self)  
Lbl_7(self) == 
               /\ _pc[self] = "Lbl_7"
               /\ cp = any
               /\ \/ /\ (Len(network[_attaque_data[self].BrokerID]) > 0)
                        /\ LET packet == Head(network[_attaque_data[self].BrokerID]) IN
                           \/ /\ (packet.type = "CONNECT")
                                 /\ LET _network == send(_attaque_data[self].BrokerID, [type |-> "CONNECT", sender |-> packet.sender]) IN
                                    /\ network' = _network
                                    /\ _pc' = [_pc EXCEPT ![self] = "CONNACK"]
                                    /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                           \/ /\ ~((packet.type = "CONNECT"))
                                    /\ _pc' = [_pc EXCEPT ![self] = "CONNACK"]
                                    /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
CONNACK(self) == 
                 /\ _pc[self] = "CONNACK"
                 /\ cp = any
                 /\ \/ /\ (Len(network[3]) > 0)
                          /\ LET packet1 == Head(network[3]) IN
                             \/ /\ (packet1.type = "CONNACK")
                                   /\ LET __attaque_data == [_attaque_data EXCEPT ![self].INJ1 = TRUE] IN
                                      LET _network == [network EXCEPT ![3] = Tail(network[3])] IN
                                      \/ /\ (__attaque_data[self].INJ1 = TRUE)
                                               /\ _attaque_data' = __attaque_data
                                               /\ network' = _network
                                               /\ _pc' = [_pc EXCEPT ![self] = "PUBLISH"]
                                               /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _stack >>
                                      \/ /\ ~((__attaque_data[self].INJ1 = TRUE))
                                               /\ _attaque_data' = __attaque_data
                                               /\ network' = _network
                                               /\ _pc' = [_pc EXCEPT ![self] = "PUBLISH"]
                                               /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _stack >>
                             \/ /\ ~((packet1.type = "CONNACK"))
                                   /\ LET _network == [network EXCEPT ![3] = Tail(network[3])] IN
                                      \/ /\ (_attaque_data[self].INJ1 = TRUE)
                                               /\ network' = _network
                                               /\ _pc' = [_pc EXCEPT ![self] = "PUBLISH"]
                                               /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                                      \/ /\ ~((_attaque_data[self].INJ1 = TRUE))
                                               /\ network' = _network
                                               /\ _pc' = [_pc EXCEPT ![self] = "PUBLISH"]
                                               /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
PUBLISH(self) == 
                 /\ _pc[self] = "PUBLISH"
                 /\ cp = any
                 /\ \/ /\ (Len(network[_attaque_data[self].BrokerID]) > 0)
                          /\ LET packet2 == Head(network[_attaque_data[self].BrokerID]) IN
                             \/ /\ (packet2.type = "PUBLISH")
                                   /\ LET _network == send(_attaque_data[self].BrokerID, [type |-> "PUBLISH", sender |-> packet2.sender, topic |-> "A", QoS |-> 2]) IN
                                      LET __attaque_data == [_attaque_data EXCEPT ![self].INJ2 = TRUE] IN
                                      \/ /\ (__attaque_data[self].INJ2 = TRUE)
                                               /\ network' = _network
                                               /\ _attaque_data' = __attaque_data
                                               /\ _pc' = [_pc EXCEPT ![self] = "PUBREL"]
                                               /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _stack >>
                                      \/ /\ ~((__attaque_data[self].INJ2 = TRUE))
                                               /\ _attaque_data' = __attaque_data
                                               /\ network' = _network
                                               /\ _pc' = [_pc EXCEPT ![self] = "PUBREL"]
                                               /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _stack >>
                             \/ /\ ~((packet2.type = "PUBLISH"))
                                   /\ \/ /\ (_attaque_data[self].INJ2 = TRUE)
                                               /\ _pc' = [_pc EXCEPT ![self] = "PUBREL"]
                                               /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                                      \/ /\ ~((_attaque_data[self].INJ2 = TRUE))
                                               /\ _pc' = [_pc EXCEPT ![self] = "PUBREL"]
                                               /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
PUBREL(self) == 
                /\ _pc[self] = "PUBREL"
                /\ cp = any
                /\ \/ /\ (Len(network[_attaque_data[self].BrokerID]) > 0)
                         /\ LET packet3 == Head(network[_attaque_data[self].BrokerID]) IN
                            \/ /\ (packet3.type = "PUBREL")
                                  /\ LET _network == send(_attaque_data[self].BrokerID, [type |-> "PUBREL", sender |-> packet3.sender, topic |-> "A", QoS |-> 2]) IN
                                     LET __attaque_data == [_attaque_data EXCEPT ![self].INJ3 = TRUE] IN
                                     \/ /\ (__attaque_data[self].INJ3 = TRUE)
                                              /\ network' = _network
                                              /\ _attaque_data' = __attaque_data
                                              /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _stack >>
                                     \/ /\ ~((__attaque_data[self].INJ3 = TRUE))
                                              /\ _attaque_data' = __attaque_data
                                              /\ network' = _network
                                              /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _stack >>
                            \/ /\ ~((packet3.type = "PUBREL"))
                                  /\ \/ /\ (_attaque_data[self].INJ3 = TRUE)
                                              /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                              /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                                     \/ /\ ~((_attaque_data[self].INJ3 = TRUE))
                                              /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                              /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
_attaque(self) == 
                      Lbl_7(self) \/ CONNACK(self) \/ PUBLISH(self) \/ PUBREL(self) \/ Lbl_1(self) \/ Lbl_2(self) \/ Lbl_3(self) \/ cqos2(self) \/ waitPUB2(self) \/ waitPUBCOMP2(self) \/ rqos2(self) \/ waitPUBREL(self)  
PubStart(self) == 
                  /\ _pc[self] = "PubStart"
                  /\ cp = any
                  /\ LET _network == send(_Publisher_data[self].BrokerID, [type |-> "CONNECT", sender |-> self]) IN
                     /\ network' = _network
                     /\ _pc' = [_pc EXCEPT ![self] = "waitCONN"]
                     /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
waitCONN(self) == 
                  /\ _pc[self] = "waitCONN"
                  /\ cp = any
                  /\ \/ /\ (Len(network[self]) > 0)
                           /\ LET packet == Head(network[self]) IN
                              \/ /\ (packet.type = "CONNACK")
                                    /\ LET __Publisher_data == [_Publisher_data EXCEPT ![self].CONNSUCC = TRUE] IN
                                       LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                       \/ /\ (__Publisher_data[self].CONNSUCC = TRUE)
                                                /\ _pc' = [_pc EXCEPT ![self] = "tryPUB2"]
                                                /\ _Publisher_data' = __Publisher_data
                                                /\ network' = _network
                                                /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _stack >>
                                       \/ /\ ~((__Publisher_data[self].CONNSUCC = TRUE))
                                                /\ _Publisher_data' = __Publisher_data
                                                /\ network' = _network
                                                /\ _pc' = [_pc EXCEPT ![self] = "PubStart"]
                                                /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _stack >>
                              \/ /\ ~((packet.type = "CONNACK"))
                                    /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                       \/ /\ (_Publisher_data[self].CONNSUCC = TRUE)
                                                /\ _pc' = [_pc EXCEPT ![self] = "tryPUB2"]
                                                /\ network' = _network
                                                /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
                                       \/ /\ ~((_Publisher_data[self].CONNSUCC = TRUE))
                                                /\ network' = _network
                                                /\ _pc' = [_pc EXCEPT ![self] = "PubStart"]
                                                /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data, _stack >>
tryPUB2(self) == 
                 /\ _pc[self] = "tryPUB2"
                 /\ cp = any
                 /\ LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[to|->_Publisher_data[self].BrokerID, PUBSUCC|->FALSE, _pc |->"Done"]>>)] IN
                    /\ _pc' = [_pc EXCEPT ![self] = "cqos2"]
                    /\ _stack' = __stack
                    /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _attaque_data, _Publisher_data >>
_Publisher(self) == 
                        PubStart(self) \/ waitCONN(self) \/ tryPUB2(self) \/ Lbl_1(self) \/ Lbl_2(self) \/ Lbl_3(self) \/ cqos2(self) \/ waitPUB2(self) \/ waitPUBCOMP2(self) \/ rqos2(self) \/ waitPUBREL(self)  

Next == (\E self \in Broker : _Broker(self))
                        \/ (\E self \in attaque : _attaque(self))
                        \/ (\E self \in Publisher : _Publisher(self))
                        \/ ((\A self \in ProcSet : _pc[self] = "Done")
                            /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Temp0 == (~ \A D \in Publisher, I \in attaque : (<> ((((_Publisher_data[D].PUBSUCC = TRUE) /\ (_attaque_data[I].INJ1 = TRUE)) /\ (_attaque_data[I].INJ2 = TRUE)) => (_attaque_data[I].INJ3 = TRUE))))

=================================================================================
