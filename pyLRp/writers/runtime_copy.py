
import sys
import os
import subprocess

class RuntimeFile(object):

    def __init__(self, fo, name):
        self.name = name
        self.fo = fo
        self.lines = iter(fo)
        self.state = ''
        self.dependencies = []
        self._parse_to_next_tag()

    def __repr__(self):
        return "<RuntimeFile at {:x}: {}>".format(id(self), self.name)

    def close(self):
        self.fo.close()

    def _parse_to_next_tag(self):
        self.state = ''
        for line in self.lines:
            if line.startswith('#% depends on '):
                line = line[len('#% depends on '):]
                self.dependencies += [file.strip() for file in line.split(',')]
                self._parse_to_next_tag()
                break
            elif line.startswith('#% start imports'):
                self.state = 'imports'
                break
            elif line.startswith('#% start classes'):
                self.state = 'classes'
                break
            elif line.startswith('#%'):
                raise Exception("Can't happen, invalid #% tag in runtime library" + line)

    def handle(self, state, outfile):
        if self.state != state:
            return

        new_name = None
        for line in self.lines:
            if new_name is not None:
                if line.startswith('def '):
                    start = 'def '
                elif line.startswith('class '):
                    start = 'class '
                else:
                    raise Exception("Can't happend invalid #% rename tag")
                line = line[:len(start)] + new_name + \
                    line[min(line.find(':'), line.find('(')):]
                new_name = None

            if line.startswith('#% end ' + state):
                self._parse_to_next_tag()
                return
            elif line.startswith('#% rename '):
                new_name = line[len('#% rename '):].strip()
            else:
                outfile.write(line)

class RuntimeCopier(object):

    def __init__(self, outfile):
        self._outfile = outfile
        self._dir = None

    def load_dir(self, python3):
        # if options[("", "")] is not None:
        #     self._dir = options[("", "")]

        if python3:
            self._dir = os.path.join(os.path.dirname(__file__), '../runtime/')

        else:
            raise NotImplementedError()

    def copy(self, files):
        try:
            file_list = []
            ordered_file_list = []
            for file in files:
                fo = open(os.path.join(self._dir, file), 'rt')
                file_list.append(RuntimeFile(fo, file))

            # XXX: the following topological sort implementation is
            # very lazy and inefficient
            file_list.sort(key=lambda x: len(x.dependencies))
            while file_list:
                if file_list[0].dependencies:
                    raise Exception("Can't happen, circular dependency in runtime library")
                newest_ordered = file_list.pop(0)
                ordered_file_list.append(newest_ordered)
                for item in file_list:
                    if newest_ordered.name in item.dependencies:
                        item.dependencies.remove(newest_ordered.name)
                file_list.sort(key=lambda x: len(x.dependencies))

            for state in ('imports', 'classes'):
                for file in ordered_file_list:
                    file.handle(state, self._outfile)

        finally:
            for fileobj in file_list:
                fileobj.close()

            for fileobj in ordered_file_list:
                fileobj.close()
