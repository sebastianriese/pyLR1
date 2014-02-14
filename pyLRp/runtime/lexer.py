#% depends on input.py
from pyLRp.runtime.input import EndOfFile

#% start classes

#% rename BaseLexer
class Lexer(object):

    def __init__(self, input_buffer):
        """
        A DFA-based Lexer.

        The `lex` method returns the tokens from `input_buffer`.
        """
        self.input_buffer_stack = []
        self.input_buffer = input_buffer
        self.next_cond = [self.CONDITION_NUMBERS["$SOF"]]
        self.token_push_back = []

    def push_back(self, token):
        self.token_push_back.append(token)

    def lex_all(self):
        tokens = []
        while True:
            type, text, pos = self.lex()
            if type == self.TOKEN_NUMBERS["$EOF"]:
                return tokens
            tokens.append((type, text, pos))

    def state_switch(self, text):
        if self.next_cond[-1] == self.CONDITION_NUMBERS["$SOF"]:
            self.next_cond[-1] = self.CONDITION_NUMBERS["$INITIAL"]

        if self.next_cond[-1] == self.CONDITION_NUMBERS["$INITIAL"] and \
                text and text[-1] == '\n':
            self.next_cond[-1] = self.CONDITION_NUMBERS["$SOL"]
        elif self.next_cond[-1] == self.CONDITION_NUMBERS["$SOL"] and  \
                text and text[-1] != '\n':
            self.next_cond[-1] = self.CONDITION_NUMBERS["$INITIAL"]

    def push_file(self, input_buffer):
        self.input_buffer_stack.append(self.input_buffer)
        self.input_buffer = input_buffer

    def pop_file(self):
        if self.input_buffer_stack:
            self.input_buffer = self.input_buffer_stack.pop()
            if self.next_cond[-1] == self.CONDITION_NUMBERS["$INITIAL"] or \
                    self.next_cond[-1] == self.CONDITION_NUMBERS["$SOL"]:
                self.next_cond[-1] = self.CONDITION_NUMBERS["$SOF"]
            return True
        else:
            return False

    def lex(self):
        if self.token_push_back:
            return self.token_push_back.pop()

        cond = self.next_cond[-1]
        state = self.starts[cond]
        table, cactions = self.tables[cond], self.actionmap[cond]
        input_buffer = self.input_buffer
        input_buffer.set_mapping(self.mappings[cond].__getitem__)
        actionvec = self.actions

        end_of_file = False

        if cactions[state] is not None:
            input_buffer.mark()
            action = actionvec[cactions[state]]
        else:
            action = None

        try:
            while True:
                state = table[state][input_buffer.step()]
                if cactions[state] is None:
                    pass
                elif cactions[state] < 0:
                    break
                else:
                    input_buffer.mark()
                    action = actionvec[cactions[state]]
        except EndOfFile:
            end_of_file = True

        if action is None:
            if end_of_file and input_buffer.not_stepped():
                if self.pop_file():
                    return self.lex()
                else:
                    return (self.TOKEN_NUMBERS["$EOF"],
                            '', input_buffer.pos())
            else:
                input_buffer.mark()
                action = self.error_action

        text, position = input_buffer.extract()

        token = action(text, position)

        self.state_switch(text)

        if token is None:
            return self.lex()
        else:
            return (token, text, position)
#% end classes
