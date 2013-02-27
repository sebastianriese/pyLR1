
class Lextable(object):

    def __init__(self, table, start, actionlist):
        self.table = table
        self.start = start
        self.actions = actionlist
        self.mapping = None


    def Get(self):
        return self.table, self.start, self.actions, self.mapping

    def ConstructEquivalenceClasses(self):
        i = 0
        classes = [[char for char in range(0,256)]]

        for line in self.table:

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

        self.mapping = [None for j in range(0,256)]
        mapping = self.mapping
        i = 0
        for cls in classes:
            for terminal in cls:
                mapping[terminal] = i
            i += 1

        newtable = []
        for line in self.table:
            newtable.append([])
            my = newtable[-1]
            for cls in classes:
                my.append(line[cls[0]])
        self.table = newtable


    def Print(self):
        print("start: %d\n" % self.start)

        for num, action in enumerate(self.actions):
            print(num, str(action))

        if not self.mapping:
            print("\n    ", end=' ')

        # print the characters
        for i in range(32, 128):
            if self.mapping:
                print(chr(i), str(self.mapping[i]))
            else:
                print(chr(i).center(2), end=' ')

        if self.mapping:
            print("\n    ", end=' ')


        printRange = range(32, 128)

        if self.mapping:
            printRange = range(len(self.table[0]))
            for i in printRange:
                print(str(i).center(2), end=' ')

        print("")
        i = 0
        for state in self.table:
            print(str(i).center(2), "-", end=' ')
            for a in printRange:
                print(str(state[a]).center(2), end=' ')
            print("")
            i+=1
