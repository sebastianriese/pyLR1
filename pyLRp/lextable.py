
class Lextable(object):

    def __init__(self, table, start, actionlist):
        self._table = table
        self._start = start
        self._actions = actionlist
        self._mapping = None


    def get(self):
        return self._table, self._start, self._actions, self._mapping

    def construct_equivalence_classes(self, alphabet):
        i = 0
        classes = [list(range(0, len(alphabet)))]

        # determine the equivalence classes
        for line in self._table:
            newclasslist = []
            for cls in classes:
                newclasses = dict()
                for char in cls:
                    state = line[char]
                    if state not in newclasses:
                        newclasses[state] = []
                    newclasses[state].append(char)
                newclasslist += list(newclasses.values())
            classes = newclasslist

        # construct the mapping from old alphabet to equivalence classes
        self._mapping = [None] * len(alphabet)
        mapping = self._mapping
        i = 0
        for cls in classes:
            for terminal in cls:
                mapping[terminal] = i
            i += 1

        # construct the new table
        newtable = []
        for line in self._table:
            newtable.append([])
            my = newtable[-1]
            for cls in classes:
                my.append(line[cls[0]])
        self._table = newtable


    def print(self):
        print("start: %d\n" % self.start)

        for num, action in enumerate(self._actions):
            print(num, str(action))

        if not self._mapping:
            print("\n    ", end=' ')

        # print the characters
        for i in range(32, 128):
            if self._mapping:
                print(chr(i), str(self._mapping[i]))
            else:
                print(chr(i).center(2), end=' ')

        if self._mapping:
            print("\n    ", end=' ')


        printRange = range(32, 128)

        if self._mapping:
            printRange = range(len(self._table[0]))
            for i in printRange:
                print(str(i).center(2), end=' ')

        print("")
        i = 0
        for state in self._table:
            print(str(i).center(2), "-", end=' ')
            for a in printRange:
                print(str(state[a]).center(2), end=' ')
            print("")
            i+=1
