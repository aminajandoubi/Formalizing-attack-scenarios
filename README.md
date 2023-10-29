# Formalizing-attack-scenarios
MQTT is a widely adopted communication protocol, particularly in the Internet of Things (IoT) context. 
Ensuring the security and reliability of MQTT is crucial to its successful implementation in various applications. 
In a previous job [1], we systematically formalized seven attack scenarios targeting the MQTT protocol using computation tree logic (CTL). 
These formalization led to twelve CTL formulas, each precisely modeling a specific attack scenario and its essential properties. 
In [2], we discuss the process of testing these attack scenarios and their CTL formulas using a formal specification based on PlusCal-2. 
The models were then translated into TLA+ proper specifications and verified using the TLC model checker. 
TLC systematically explores the model's state space to determine whether the desired properties are satisfied during this exploration.
We successfully demonstrated eight of the attack scenarios formulated using this formal approach. 
However, four scenarios could not be verified due to the limitations of the existing specification. 
This observation underlines the need for a more comprehensive specification covering all MQTT protocol aspects. 
In response, we propose detailed corrections and improvements to the specification based on execution traces obtained by TLC. 
Our work highlights the importance of formal verification in assessing the reliability and security of the MQTT protocol.
[1] : https://sites.google.com/view/cups2023/proceedings?authuser=0
[2] : Work in progress published
