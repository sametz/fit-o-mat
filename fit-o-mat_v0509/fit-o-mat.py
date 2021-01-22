#!/usr/bin/python3
'''
Fit-o-mat - a versatile program for non-linear least-squares fitting
Copyright (C) 2017-2018  Andreas Moeglich, University of Bayreuth, Germany
contact me at andreas.moeglich@uni-bayreuth.de

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software Foundation,
Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301  USA
'''
VERSION = '0.509'

from PyQt5 import QtCore, QtGui, QtWidgets
import sys
import glob
from functools import partial
import copy
import ast
from os.path import expanduser
import webbrowser

import matplotlib
matplotlib.use("Qt5Agg")
import matplotlib.pyplot as plt
from matplotlib.widgets import RectangleSelector as RectSel
from matplotlib.backends.backend_qt5agg import FigureCanvasQTAgg as FigureCanvas
from matplotlib import patheffects as PathEffects
import xlrd
import xlsxwriter
import numpy as np
import scipy.optimize as optim

# reimplement FigureCanvas to optimize graphics refresh  
class MyFigureCanvas(FigureCanvas):
  def __init__(self, parent=None, matplotlibCanvas=None, name='superunknown'):
    super(MyFigureCanvas, self).__init__(parent)
    self.parent = parent
    self.matplotlibCanvas = matplotlibCanvas
    self.refreshCount = 0
    self.destructCounter = 0
    self.name = name
    
  def myRefresh(self):
    # wrapper function to globally set how draw updates are done
    self.refreshCount += 1
    
    # ready to destruct?
    if(self.destructCounter):
      self.destructCounter -= 1
      if(not self.destructCounter):
        self.matplotlibCanvas.destructAboutLogo()
    
    # do we have arrows to take care of?
    for entry in ['x', 'y']:
      if(self.matplotlibCanvas.handleArrow[entry] != None):
        self.matplotlibCanvas.drawAxisArrow(axis=entry, redraw=False, target='plot')
      if(self.matplotlibCanvas.handleArrowResid[entry] != None):
        self.matplotlibCanvas.drawAxisArrow(axis=entry, redraw=False, target='resid')

    # the actual draw command
    self.draw()
    
  def setDestructionCounter(self, counter=0):
    # sets up destruction of self.handlesAbout
    self.destructCounter = counter

  def getDestructionCounter(self):
    # returns destruction counter
    return self.destructCounter

# custom QComboBox to fix Qt layout bug on Mac :(
class QComboBoxMac(QtWidgets.QComboBox):
  def __init__(self, *args, **kwargs):
    super(QComboBoxMac, self).__init__(*args, **kwargs)
    self.setAttribute(QtCore.Qt.WA_LayoutUsesWidgetRect)

# custom QPushButton to fix Qt layout bug on Mac :(
class QPushButtonMac(QtWidgets.QPushButton):
  def __init__(self, *args, **kwargs):
    super(QPushButtonMac, self).__init__(*args, **kwargs)
    self.setAttribute(QtCore.Qt.WA_LayoutUsesWidgetRect)

# custom QWidget to fix Qt layout bug on Mac :(
class QWidgetMac(QtWidgets.QWidget):
  def __init__(self, *args, **kwargs):
    super(QWidgetMac, self).__init__(*args, **kwargs)
    self.setAttribute(QtCore.Qt.WA_LayoutUsesWidgetRect)

# custom-styled QMenu
class KuhMenu(QtWidgets.QMenu):
  def __init__(self, *args, **kwargs):
    super(KuhMenu, self).__init__(*args, **kwargs)
    self.borderRadius = scaledDPI(5)
    
  def paintEvent(self, event):
    # draw rounded corners
    s = self.size()
    qp = QtGui.QPainter()
    qp.begin(self)
    qp.setRenderHint(QtGui.QPainter.Antialiasing, True)
    qp.drawRoundedRect(0, 0, s.width(), s.height(), self.borderRadius, self.borderRadius)
    qp.end()    
    
# a delegate for custom display of float numbers
class FloatFormatDelegate(QtWidgets.QStyledItemDelegate):
  def __init__(self):
    super(FloatFormatDelegate, self).__init__()

  def displayText(self, value, locale):
    if(type(value) == float):
      return QtWidgets.QStyledItemDelegate.displayText(self, value, locale).replace(',', '.')
    else:
      return QtWidgets.QStyledItemDelegate.displayText(self, value, locale)
  
# custom table model for speeding up data loading (QTableView vs. QTableWidget)
class TableModel(QtCore.QAbstractTableModel):
  def __init__(self, data, parent=None):
    super(TableModel, self).__init__(parent)
    self.parent = parent
    if(hasattr(data, 'tolist')):
      # deal with numpy data
      self._data = data.tolist()
    else:
      self._data = data
    self.headers = [str(i+1) for i in range(self.columnCount())]

  def rowCount(self, parent=None):
    return len(self._data)

  def columnCount(self, parent=None):
    return len(self._data[0]) if self.rowCount() else 0

  def data(self, index, role=QtCore.Qt.DisplayRole):
    if role == QtCore.Qt.DisplayRole:
      row = index.row()
      if 0 <= row < self.rowCount():
        column = index.column()
        if 0 <= column < self.columnCount():
          return self._data[row][column]
        
  def dataByIndices(self, row=0, column=0):
    if 0 <= row < self.rowCount():
      if 0 <= column < self.columnCount():
        return self._data[row][column]
        
  def headerData(self, section, orientation, role=QtCore.Qt.DisplayRole):
    if role == QtCore.Qt.DisplayRole and orientation == QtCore.Qt.Horizontal:
      if(section<len(self.headers)):
        return self.headers[section]
      else:
        # needed for UI calls while table empty
        return ''
    return QtCore.QAbstractTableModel.headerData(self, section, orientation, role)        

  def setAllHeaders(self, headerData):
    maxIndex = min(self.columnCount(), len(headerData))
    self.headers[:maxIndex] = headerData[:maxIndex]

  def setSingleHeader(self, index, label):
    if(index < self.columnCount()):
      self.headers[index] = label
      
  def getDataRows(self, indices):
    retv = [self._data[index] for index in indices]
    return retv

  def getHeaders(self):
    return self.headers

  def getAllData(self):
    return self._data
  
  def setData(self, value, row, column):
    if((0 <= row < self.rowCount()) and (0 <= column < self.columnCount())):
      self._data[row][column] = value

  def pasteDataBlock(self, data, offsetRow=0, offsetColumn=0):
    for row in data:
      if(offsetRow < self.rowCount()):
        rowItems = len(row)
        self._data[offsetRow][offsetColumn:offsetColumn + rowItems] = row
      offsetRow += 1

# a custom cursor
class MyCursor(matplotlib.widgets.Cursor):
  def __init__(self, *args, **kwargs):
    super(MyCursor, self).__init__(*args, **kwargs)
    self.label = self.ax.text(1, 1, 'Hallo', animated=True)
    self.label.set_fontsize(scaledDPI(12))
    # need to store background for initial creation of cursor
    self.background = self.canvas.copy_from_bbox(self.ax.bbox)
    
  def onmove(self, event):
    """on mouse motion draw the cursor if visible"""
    if self.ignore(event):
      return
    if not self.canvas.widgetlock.available(self):
      return
    if event.inaxes != self.ax:
      self.linev.set_visible(False)
      self.lineh.set_visible(False)
      self.label.set_visible(False)

      if self.needclear:
        self.canvas.draw()
        self.needclear = False
      return
    self.needclear = True
    if not self.visible:
      return
    
    self.refreshCrossHair(event)
    # check whether we are on canvas
    if ((event.xdata != None) and (event.ydata != None)):
      self._update()

  def refreshCrossHair(self, event):
    # update cross hair
    self.linev.set_xdata((event.xdata, event.xdata))
    self.lineh.set_ydata((event.ydata, event.ydata))
    self.linev.set_visible(self.visible and self.vertOn)
    self.lineh.set_visible(self.visible and self.horizOn)
    # update label position
    self.label.set_x(event.xdata)
    self.label.set_y(event.ydata)
    self.label.set_visible(self.visible)
    # check whether we are on canvas
    if ((event.xdata != None) and (event.ydata != None)):
      self.label.set_text('(' + self.formatNumber(event.xdata) + '/' + self.formatNumber(event.ydata) + ')')
    # update color
    canvasColor = self.ax.patch.get_facecolor()
    if(sum(canvasColor[0:3]) > 1.5):
      color = 'black'
    else:
      color = 'white'
    self.label.set_color(color)
    self.lineh.set_color(color)
    self.linev.set_color(color)
    # check quadrant of plot
    if(event.x > ((self.ax.bbox.xmin + self.ax.bbox.xmax) / 2.0)):
      self.label.set_horizontalalignment('right')
    else:
      self.label.set_horizontalalignment('left')
    if(event.y > ((self.ax.bbox.ymin + self.ax.bbox.ymax) / 2.0)):
      self.label.set_verticalalignment('top')
    else:
      self.label.set_verticalalignment('bottom')

  def getHandles(self):
    # returns handles to graphics elements
    handles = [self.linev, self.lineh, self.label]
    return handles

  def _update(self):
    if self.useblit:
      if self.background is not None:
        self.canvas.restore_region(self.background)
      self.ax.draw_artist(self.linev)
      self.ax.draw_artist(self.lineh)
      self.ax.draw_artist(self.label)
      self.canvas.blit(self.ax.bbox)
    else:
      self.canvas.draw_idle()

    return False

  def toggleVisibility(self, state=False, event=None):
    self.visible = state
    if(self.visible and (event != None)):
      self.refreshCrossHair(event)
    else:
      self.linev.set_visible(self.visible and self.vertOn)
      self.lineh.set_visible(self.visible and self.horizOn)
      self.label.set_visible(self.visible)
    # check whether we are on canvas
    if ((event.xdata != None) and (event.ydata != None)):
      self._update()

  def formatNumber(self, number):
    # formats number for output
    NUMBER_SWITCH = 1e3
    FORMAT_DECIMAL = '{:.3f}'
    FORMAT_SCIENTIFIC = '{:.3e}'
    # determine return string
    if((self.isNumber(number)) and (np.isfinite(float(number)))):
      if((np.abs(number)>NUMBER_SWITCH) or (np.abs(number)<1.0/NUMBER_SWITCH)):
        numberstr = FORMAT_SCIENTIFIC.format(number)
      else:
        numberstr = FORMAT_DECIMAL.format(number)
    else:
      numberstr = str(number)
    
    return numberstr

  def isNumber(self, s):
    # checks whether string is a number
    try:
      float(s)
      return True
    except ValueError:
      pass
   
    try:
      import unicodedata
      unicodedata.numeric(s)
      return True
    except (TypeError, ValueError):
      pass
    
    return False
  
# a QLineEdit that finally behaves as I want
class QLineEditClick(QtWidgets.QLineEdit):
  def __init__(self, argument = None):
    super(QLineEditClick, self).__init__(argument)
    self._gainedFocus = False
    self._originalMousePressEvent = QtWidgets.QLineEdit.mousePressEvent
    self._originalFocusInEvent = QtWidgets.QLineEdit.focusInEvent

  def focusInEvent(self, event):
    self._originalFocusInEvent(self, event)
    self.selectAll()
    
    # determine how we got focus (0 is via mouse action)
    if(event.reason() == 0):
      self._gainedFocus = True
    
  def mousePressEvent(self, event):
    self._originalMousePressEvent(self, event)
    if(self._gainedFocus):
      self.selectAll()
      self._gainedFocus = False

# the data table widget
class DataTable(QtWidgets.QTableView):
  def __init__(self, parent=None):
    super(DataTable, self).__init__(parent)
    self.setEditTriggers(QtWidgets.QAbstractItemView.NoEditTriggers)
    self.parent = parent
    self.tableModel = None
    self.currentRow, self.currentCol = 0, 0
    self.pageStep = 20
    # connect click event on table header
    hheader = self.horizontalHeader()
    hheader.sectionClicked.connect(self.changeRole)

  def configTable(self, dimx, dimy, retainRoles=False, retainSelection=False, init=False):
    # helper function called by different file importers
    # set row height and prevent from resizing
    self.rowHeight = int(self.fontMetrics().height() + scaledDPI(2))
    if(init):
      self.rowHeight = scaledDPI(18)
    vheader = self.verticalHeader()
    vheader.setDefaultSectionSize(self.rowHeight)
    for entry in range(dimy):
      vheader.setSectionResizeMode(entry, QtWidgets.QHeaderView.Fixed)
      
    # set col width
    self.colWidth = int(self.size().width() / 4.5)
    hheader = self.horizontalHeader()
    if(not init):
      hheader.setDefaultSectionSize(self.colWidth)
    
    # set selection mode
    self.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectRows)
    
    # select all
    if(not retainSelection):
      self.selectAll()
    
    # connect event for selection update
    self.selectionModel().selectionChanged.connect(partial(self.parent.updateData, True))
    self.selectionModel().currentChanged.connect(self.currentCellChanged)
    
    # assign roles to columns (-1 means role is undefined)
    if(retainRoles):
      for item in ['x', 'y', 'xerr', 'yerr', 'labels']:
        if(item in self.roles):
          # check whether target column is available
          if(self.roles[item] >= dimx):
            self.roles[item] = -1
        else:
          self.roles[item] = -1
    else:
      self.roles = {'x':-1, 'y':-1, 'xerr':-1, 'yerr':-1, 'labels':-1}
      if (dimx):
        self.roles['x'] = 0
        if (dimx == 2):
          self.roles['y'] = 1
        elif(dimx >= 3):
          self.roles['y'] = 1
          self.roles['yerr'] = 2
    self.rolestr = {'x':'x', 'y':'y', 'xerr':u'\N{GREEK CAPITAL LETTER DELTA}x', 'yerr':u'\N{GREEK CAPITAL LETTER DELTA}y', 'labels':'labels'}
    # asisgn numbered column headers
    headerData = [str(i+1) for i in range(dimx)]
    # update headers for roles
    for key in self.roles:
      if(self.roles[key]+1):
        headerData[self.roles[key]] = str(self.roles[key]+1)+' ('+self.rolestr[key]+')'
    self.tableModel.setAllHeaders(headerData)
    self.setModel(self.tableModel)

    self.setItemDelegate(FloatFormatDelegate())
    self.setFocus()

  def killTheComma(self):
    # processes sheet data and replaces all commata by period
    if(len(self.sheetData)):
      dimx, dimy = len(self.sheetData[0]), len(self.sheetData)
      nuData = []
      for row in self.sheetData:
        nuData.append([self.killHelper(i) for i in row])
        
      self.sheetData = nuData
      self.tableModel = TableModel(self.sheetData, self)
      self.configTable(dimx, dimy, retainRoles=True, retainSelection=False)
      self.selectAll()

      nuIndex = self.model().index(self.currentRow, self.currentCol)
      self.selectionModel().setCurrentIndex(nuIndex, QtCore.QItemSelectionModel.Select)
      self.tableModel.layoutChanged.emit()
      
      # for some strange reason we have to connect the event again, grrrr! (should've been done in self.configTable())
      self.selectionModel().currentChanged.connect(self.currentCellChanged)
      
  def killHelper(self, item):
    if(type(item) in [int, float]):
      return item
    elif((type(item) == str) and (',' in item)):
      convItem = item.replace(',', '.')
      try:
        convItem = float(convItem)
        return convItem
      except:
        return item
    else:
      return item

  def generateEmptyTable(self, columnCount=4, rowCount=20):
    # intializes blank table
    blankData = [[''] * columnCount for i in range(rowCount)]
    self.sheetData = blankData
    self.tableModel = TableModel(self.sheetData, self)
    self.setModel(self.tableModel)
    self.configTable(columnCount, rowCount, init=True)

    self.clearSelection()
    if(rowCount):
      self.selectRow(0)
    nuIndex = self.model().index(self.currentRow, self.currentCol)
    self.selectionModel().setCurrentIndex(nuIndex, QtCore.QItemSelectionModel.Select)
    self.tableModel.layoutChanged.emit()    

  def restoreTable(self, tableData=[]):
    # used by loadState fxn
    if(len(tableData)):
      self.currentRow, self.currentCol = 0, 0
      self.sheetData = tableData
      self.tableModel = TableModel(self.sheetData, self)
      self.setModel(self.tableModel)
      
      dimx, dimy = len(tableData[0]), len(tableData)
      self.configTable(dimx, dimy)
      
      nuIndex = self.model().index(self.currentRow, self.currentCol)
      self.selectionModel().setCurrentIndex(nuIndex, QtCore.QItemSelectionModel.Select)
      self.tableModel.layoutChanged.emit()    

  def loadXLS(self, filename, transpose=False):
    # open XLS sheet
    QtWidgets.QApplication.setOverrideCursor(QtGui.QCursor(QtCore.Qt.WaitCursor))
    QtCore.QCoreApplication.processEvents()
    try:
      self.wb = xlrd.open_workbook(filename)
    except:
      self.parent.parent.statusbar.showMessage('Cannot load file ' + filename, self.parent.parent.STATUS_TIME)
    else:
      self.sheetNames = self.wb.sheet_names()
      
      # update number of available sheets and current sheet
      self.parent.resetSheetSpinBox(currVal=1, maxVal=self.wb.nsheets, currName=self.sheetNames[0])
      
      # initally assume data is on first sheet
      self.sheet = self.wb.sheet_by_index(0)
      (dimx, dimy) = (self.sheet.ncols, self.sheet.nrows)
      
      # populate the table
      self.sheetData = []
      for entry in range(dimy):
        row = self.sheet.row_values(entry)
        self.sheetData.append(row)
        
      # transpose data?
      if((transpose) and (len(self.sheetData))):
        transposedData = []
        for entry1 in range(len(self.sheetData[0])):
          row = []
          for entry2 in range(len(self.sheetData)):
            row.append(self.sheetData[entry2][entry1])
          transposedData.append(row)
        self.sheetData = transposedData
        dimx, dimy = dimy, dimx
      
      self.tableModel = TableModel(self.sheetData, self)
      self.setModel(self.tableModel)
      
      # configure table
      self.configTable(dimx, dimy)

    QtWidgets.QApplication.restoreOverrideCursor()
  
  def changeSheet(self, currVal=1, transpose=False):
    # update number of available sheets and current sheet
    self.parent.resetSheetSpinBox(currVal=currVal, maxVal=self.wb.nsheets, currName=self.sheetNames[currVal - 1])

    # changes sheet in multi-sheet Excel file
    self.sheet = self.wb.sheet_by_index(currVal - 1)
    (dimx, dimy) = (self.sheet.ncols, self.sheet.nrows)
    
    # populate the table
    self.sheetData = []
    for entry in range(dimy):
      row = self.sheet.row_values(entry)
      self.sheetData.append(row)
    
    # transpose data?
    if((transpose) and (len(self.sheetData))):
      transposedData = []
      for entry1 in range(len(self.sheetData[0])):
        row = []
        for entry2 in range(len(self.sheetData)):
          row.append(self.sheetData[entry2][entry1])
        transposedData.append(row)
      self.sheetData = transposedData
      dimx, dimy = dimy, dimx
      
    self.tableModel = TableModel(self.sheetData, self)
    self.setModel(self.tableModel)

    # configure table
    self.configTable(dimx, dimy, retainRoles=True)

  def transposeTable(self):
    # takes current data table and transposes contents
    if(self.tableModel != None):
      currData = self.tableModel.getAllData()
      
      # transpose data
      if(len(currData)):
        transposedData = []
        for entry1 in range(len(currData[0])):
          row = []
          for entry2 in range(len(currData)):
            row.append(currData[entry2][entry1])
          transposedData.append(row)
        self.sheetData = transposedData
        dimx, dimy = len(self.sheetData[0]), len(self.sheetData)
        
      self.tableModel = TableModel(self.sheetData, self)
      self.setModel(self.tableModel)
  
      # configure table
      self.configTable(dimx, dimy, retainRoles=True)

  def loadTextFile(self, filename, delimiter='\t', transpose=False):
    # open a text file
    QtWidgets.QApplication.setOverrideCursor(QtGui.QCursor(QtCore.Qt.WaitCursor))
    QtCore.QCoreApplication.processEvents()
    try:
      # try opening text file
      readhandle = open(filename, 'r')
      filecontent = readhandle.readlines()
    except:
      self.parent.parent.statusbar.showMessage('Cannot load file ' + filename, self.parent.parent.STATUS_TIME)
    else:
      readhandle.close()
      
      # determine row and col count
      filecontent = [i.rstrip() for i in filecontent]
      dimy = len(filecontent)
      dimx = max([i.count(delimiter) for i in filecontent]) + 1

      # turn off multiple sheet option
      self.parent.resetSheetSpinBox(currVal=1, maxVal=1, currName='')
      
      # populate the table
      maxNumberItems = 0
      self.sheetData = []
      for row in filecontent:
        splitline = row.split(delimiter)
        splitline = [float(i) if self.isNumber(i) else i for i in splitline]
        self.sheetData.append(splitline)
        maxNumberItems = np.max((maxNumberItems, len(splitline)))
      
      # fill sheetData with empty cells to make square (otherwise will have problems in TableModel)
      for entry in self.sheetData:
        while(len(entry) < maxNumberItems):
          entry.append('')

      # transpose data?
      if((transpose) and (len(self.sheetData))):
        transposedData = []
        for entry1 in range(len(self.sheetData[0])):
          row = []
          for entry2 in range(len(self.sheetData)):
            row.append(self.sheetData[entry2][entry1])
          transposedData.append(row)
        self.sheetData = transposedData
        dimx, dimy = dimy, dimx

      self.tableModel = TableModel(self.sheetData, self)
      self.setModel(self.tableModel)

      # configure table
      self.configTable(dimx, dimy)

    QtWidgets.QApplication.restoreOverrideCursor()

  def changeRole(self, col):
    # open context menu to assign roles
    options = ['x', 'xerr', 'y', 'yerr', 'labels']
    self.menu = QtWidgets.QMenu(self)
    self.menu.setTitle('Assign role')
    
    for entry in options:
      action = QtWidgets.QAction(self.rolestr[entry], self)
      action.triggered.connect(partial(self.changeRoleHelper, col, entry))
      self.menu.addAction(action)
      
    action = QtWidgets.QAction('none', self)
    action.triggered.connect(partial(self.clear_role, col))
    self.menu.addAction(action)

    # apply styles to popup window
    if(QSTYLE != None):
      self.menu.setStyle(QSTYLE)
    if(QSTYLESHEET != None):
      self.menu.setStyleSheet(QSTYLESHEET)
      
    # display menu at current mouse pointer
    self.menu.popup(QtGui.QCursor.pos())
  
  def changeRoleHelper(self, col, role):
    # actually assigns the new role
    # did this column have any role assigned?
    for key in self.roles:
      if(self.roles[key] == col):
        self.roles[key] = -1
    
    # is the new role already taken?
    if (self.roles[role]+1):
      # reset old label
      self.tableModel.setSingleHeader(self.roles[role], str(self.roles[role]+1))
      
    # assign new role
    self.roles[role] = col
    self.tableModel.setSingleHeader(col, str(col+1)+' ('+self.rolestr[role]+')')
    self.tableModel.layoutChanged.emit()
    
    # trigger data update
    self.parent.updateData(docheck = True)

  def clear_role(self, col):
    # unassigns role of column
    # did this column have any role assigned?
    for key in self.roles:
      if(self.roles[key] == col):
        self.roles[key] = -1
        
    # reset label
    self.tableModel.setSingleHeader(col, str(col+1))
    self.tableModel.layoutChanged.emit()

    # trigger data update
    self.parent.updateData(docheck = True)

  def hasComma(self):
    # cycles through selected cells and checks for presence of comma
    selind = self.selectionModel().selectedIndexes()
    retv = False
    index = 0
    while((not retv) and (index < len(selind))):
      if((type(selind[index].data()) == str) and (',' in selind[index].data())):
        retv = True
      index += 1

    return retv
    
  def getData(self):
    # returns selected data as numpy array
    # determine selected rows
    selind = self.selectionModel().selectedRows()
    selind = sorted([i.row() for i in selind])
     
    # retrieve data from table
    retv = []; roles = []
    # check whether at least x and y assigned
    if ((self.roles['x']+1) and (self.roles['y']+1)):
      if (len(selind)):
        # get all selected data rows
        selectedData = self.tableModel.getDataRows(selind)

        # deal with labels separately to allow non-numerical entries here
        if(self.roles['labels'] > -1):
          selectedLabels = []
          index = self.roles['labels']
          for entry in selectedData:
            selectedLabels.append(entry[index])
        
        # reduce data to columns we are interested in
        activeKeys = [key for key in ['x', 'xerr', 'y', 'yerr'] if (self.roles[key] > -1)]
        indices = [self.roles[key] for key in activeKeys]
        for index, entry in enumerate(selectedData):
          selectedData[index] = [entry[i] for i in indices]
          
        # prepare list for numpy array
        prunedData = []; no_items = len(activeKeys)
        for index, row in enumerate(selectedData):
          types = [1 if type(i) in [int, float] else 0 for i in row]
          if(np.sum(types) == no_items):
            # only numerical entries on row
            if(self.roles['labels'] > -1):
              row.append(selectedLabels[index])
            prunedData.append(row)
          elif(np.sum(types) > 0):
            # at least one numerical entry on row
            lengths = [len(i) for index, i in enumerate(row) if(not types[index])]
            if(np.sum(lengths) == 0):
              # all other cells empty => replace by zero
              row = [i if types[index] else 0.0 for index, i in enumerate(row)]
              if(self.roles['labels'] > -1):
                row.append(selectedLabels[index])
              prunedData.append(row)
        
        # convert nested list to numpy array
        retv = prunedData
        roles = activeKeys
        if(self.roles['labels'] > -1):
          roles.append('labels')
    
        # sort data by ascending x values
        #if(len(retv)):
          # will sort according to first entry w/in nested list which should be 'x'
        #  retv = sorted(retv)
        # turned off this feature as it causes problems for cyclic data (e.g., voltammetry)
    return retv, roles

  def keyPressEvent(self, event):
    if event.matches(QtGui.QKeySequence.Copy):
      # prepare output
      selind = self.selectionModel().selectedRows()
      selind = sorted([i.row() for i in selind])      
      # get data
      selectedData = self.tableModel.getDataRows(selind)
      output = []
      for row in selectedData:
        row = [str(i) for i in row]
        output.append('\t'.join(row))
      output = '\n'.join(output)
      clipboard = QtWidgets.QApplication.clipboard()
      clipboard.setText(output)
    elif event.matches(QtGui.QKeySequence.Paste):
      clipboard = QtWidgets.QApplication.clipboard()
      clipMime = clipboard.mimeData()
      # check wether clip object contains text
      if(clipMime.hasText()):
        clipContent = clipboard.text()
        self.pasteText(pastedText=clipContent)
    elif event.matches(QtGui.QKeySequence.SelectAll):
      self.selectAll()
    elif(event.key() == QtCore.Qt.Key_Down):
      if(self.currentRow < self.tableModel.rowCount() - 1):
        if(not (event.modifiers() & QtCore.Qt.ShiftModifier)):
          self.clearSelection()
        self.currentRow += 1
        self.selectTo(self.currentRow, self.currentRow)
        nuIndex = self.model().index(self.currentRow, self.currentCol)
        self.selectionModel().setCurrentIndex(nuIndex, QtCore.QItemSelectionModel.Select)
    elif(event.key() == QtCore.Qt.Key_Up):
      if(self.currentRow > 0):
        if(not (event.modifiers() & QtCore.Qt.ShiftModifier)):
          self.clearSelection()
        self.currentRow -= 1
        self.selectTo(self.currentRow, self.currentRow)
        
        nuIndex = self.model().index(self.currentRow, self.currentCol)
        self.selectionModel().setCurrentIndex(nuIndex, QtCore.QItemSelectionModel.Select)
    elif(event.key() == QtCore.Qt.Key_PageDown):
      if(self.currentRow < self.tableModel.rowCount() - 1):
        if(not (event.modifiers() & QtCore.Qt.ShiftModifier)):
          self.clearSelection()
        origRow = self.currentRow
        self.currentRow += self.pageStep
        self.currentRow = min(self.currentRow, self.tableModel.rowCount() - 1)
        if(not (event.modifiers() & QtCore.Qt.ShiftModifier)):
          origRow = self.currentRow
        self.selectTo(origRow, self.currentRow)
        nuIndex = self.model().index(self.currentRow, self.currentCol)
        self.selectionModel().setCurrentIndex(nuIndex, QtCore.QItemSelectionModel.Select)
    elif(event.key() == QtCore.Qt.Key_PageUp):
      if(self.currentRow > 0):
        if(not (event.modifiers() & QtCore.Qt.ShiftModifier)):
          self.clearSelection()
        origRow = self.currentRow
        self.currentRow -= self.pageStep
        self.currentRow = max(self.currentRow, 0)
        if(not (event.modifiers() & QtCore.Qt.ShiftModifier)):
          origRow = self.currentRow
        self.selectTo(origRow, self.currentRow)
        nuIndex = self.model().index(self.currentRow, self.currentCol)
        self.selectionModel().setCurrentIndex(nuIndex, QtCore.QItemSelectionModel.Select)
    elif(event.key() in [QtCore.Qt.Key_Left, QtCore.Qt.Key_Right]):
      # ignore event such that we can capture the left/right keys
      event.ignore()
      flag = False
      if(event.key() == QtCore.Qt.Key_Left):
        if(self.currentCol > 0):
          self.currentCol -= 1
          flag = True
      elif(self.currentCol < self.tableModel.columnCount() - 1):
        self.currentCol += 1
        flag = True
      if(flag):
        nuIndex = self.model().index(self.currentRow, self.currentCol)
        self.selectionModel().setCurrentIndex(nuIndex, QtCore.QItemSelectionModel.Select)
    elif(event.key() in [QtCore.Qt.Key_Home, QtCore.Qt.Key_End]):
      if(event.modifiers() & QtCore.Qt.ControlModifier):
        flag = False
        if(event.key() == QtCore.Qt.Key_Home):
          if(self.currentRow > 0):
            origRow = self.currentRow
            self.currentRow = 0
            flag = True
        elif(self.currentRow < self.tableModel.rowCount() - 1):
          origRow = self.currentRow
          self.currentRow = self.tableModel.rowCount() - 1
          flag = True
        if(flag):
          if(not (event.modifiers() & QtCore.Qt.ShiftModifier)):
            self.clearSelection()
            origRow = self.currentRow
          self.selectTo(origRow, self.currentRow)
          nuIndex = self.model().index(self.currentRow, self.currentCol)
          self.selectionModel().setCurrentIndex(nuIndex, QtCore.QItemSelectionModel.Select)
      else:
        flag = False
        if(event.key() == QtCore.Qt.Key_Home):
          if(self.currentCol > 0):
            self.currentCol = 0
            flag = True
        elif(self.currentCol < self.tableModel.columnCount() - 1):
          self.currentCol = self.tableModel.columnCount() - 1
          flag = True
        if(flag):
          nuIndex = self.model().index(self.currentRow, self.currentCol)
          self.selectionModel().setCurrentIndex(nuIndex, QtCore.QItemSelectionModel.Select)
    elif(event.key() in [QtCore.Qt.Key_Tab, QtCore.Qt.Key_Backtab]):
      # advance cell on tab
      if(event.key() == QtCore.Qt.Key_Backtab):
        self.currentCol -= 1
        if(self.currentCol < 0):
          if(self.currentRow > 0):
            self.currentRow -= 1
            self.currentCol = self.tableModel.columnCount() - 1
          else:
            self.currentCol = 0
      else:
        self.currentCol += 1
        if(self.currentCol >= self.tableModel.columnCount()):
          if(self.currentRow < self.tableModel.rowCount() - 1):
            self.currentRow += 1
            self.currentCol = 0
          else:
            self.currentCol = self.tableModel.columnCount() - 1
      self.clearSelection()
      self.selectTo(self.currentRow, self.currentRow)
      nuIndex = self.model().index(self.currentRow, self.currentCol)
      self.selectionModel().setCurrentIndex(nuIndex, QtCore.QItemSelectionModel.Select)
    elif(event.key() in [QtCore.Qt.Key_Backspace, QtCore.Qt.Key_Delete]):
      # clear current cell
      self.tableModel.setData('', self.currentRow, self.currentCol)
      # refresh table view
      cellIndex = self.tableModel.index(self.currentRow, self.currentCol)
      self.tableModel.dataChanged.emit(cellIndex, cellIndex, [QtCore.Qt.DisplayRole])
    elif (event.matches(QtGui.QKeySequence.Save) or event.matches(QtGui.QKeySequence.Open) or event.matches(QtGui.QKeySequence.HelpContents) or event.matches(QtGui.QKeySequence.Print) or event.matches(QtGui.QKeySequence.Quit)):
      # pass event to main ui
      event.ignore()
    elif(not (event.key() in [QtCore.Qt.Key_Escape])):
      openDialog = False
      if(event.key() in [QtCore.Qt.Key_Enter, QtCore.Qt.Key_Return]):
        openDialog = True
        initialEdit = ''
      elif(len(event.text())):
        openDialog = True
        initialEdit = event.text()
      if(openDialog):
        # ensure that cell is visible
        indexAt = self.model().index(self.currentRow, self.currentCol)
        self.scrollTo(indexAt)
        # open edit QMenu at cell position
        rowViewport, colViewport = self.rowViewportPosition(self.currentRow), self.columnViewportPosition(self.currentCol) + self.verticalHeader().width()
        menuPos = self.mapToGlobal(QtCore.QPoint(colViewport, rowViewport))
        self.menu = EditDataMenu(parent=self, tableModel=self.tableModel, indexAt=indexAt, initialEdit=initialEdit)
        # apply styles to popup window
        if(QSTYLE != None):
          self.menu.setStyle(QSTYLE)
        if(QSTYLESHEET != None):
          self.menu.setStyleSheet(QSTYLESHEET)
        self.menu.popup(menuPos)    

  def selectTo(self, startRow=0, endRow=0):
    # selects target rows
    lowRow, hiRow = min(startRow, endRow), max(startRow, endRow)
    columnCount = self.tableModel.columnCount()
    
    topLeft = self.model().index(lowRow, 0)
    bottomRight = self.model().index(hiRow, columnCount - 1)
    itemSelection = QtCore.QItemSelection(topLeft, bottomRight)
    self.selectionModel().select(itemSelection, QtCore.QItemSelectionModel.Select)

  def pasteText(self, pastedText=''):
    # store target cell
    offsetRow, offsetColumn = self.currentRow, self.currentCol
    # determine size of text to be pasted
    clipRows = pastedText.split('\n')
    clipCols = [i.split('\t') for i in clipRows]
    clipColCount = [len(i) for i in clipCols]
    # determine new data sheet dimensions
    nuRowCount, nuColCount = len(clipRows), max(clipColCount)
    # check for trailing all-empty columns which we won't copy
    index = nuColCount - 1
    trailCol = nuColCount
    while(index >= 0):
      for entry in clipCols:
        if(0 < index < len(entry)):
          if(len(entry[index])):
            trailCol = index + 1
            index = -1
      index -= 1
    # make clipped text square and truncate after trailCol
    clipCols = [i + ([''] * nuColCount) for i in clipCols]
    clipCols = [i[:trailCol] for i in clipCols]
    # convert to number where possible
    clipCols = [[float(j) if self.isNumber(j) else j for j in i] for i in clipCols]
    # prepare pasting of text -- resize if needed
    dimy, dimx = self.tableModel.rowCount(), self.tableModel.columnCount()
    if(((offsetColumn + trailCol) > dimx) or ((offsetRow + nuRowCount) > dimy)):
      # store current data
      currData = self.tableModel.getAllData()
      # blank data
      dimx, dimy = max(dimx, offsetColumn + trailCol), max(dimy, offsetRow + nuRowCount)
      blankData = [[''] * dimx for i in range(dimy)]
      self.tableModel = TableModel(blankData, self)
      self.setModel(self.tableModel)
      # restore original data
      self.tableModel.pasteDataBlock(data=currData, offsetRow=0, offsetColumn=0)
    
    # paste new data
    self.tableModel.pasteDataBlock(data=clipCols, offsetRow=offsetRow, offsetColumn=offsetColumn)
    self.configTable(offsetColumn + trailCol, offsetRow + nuRowCount, retainRoles=True, retainSelection=True)
    self.tableModel.layoutChanged.emit()
    
  def mouseDoubleClickEvent(self, event):
    # allow editing of cell on double click
    # perform original event
    QtWidgets.QTableView.mouseDoubleClickEvent(self, event)
    
    # determine indices of clicked cell and scroll to ensure visibility
    indexAt = self.indexAt(event.pos())
    self.scrollTo(indexAt)
    row, col = indexAt.row(), indexAt.column()
    rowViewport, colViewport = self.rowViewportPosition(row), self.columnViewportPosition(col)
    
    # open edit QMenu at cell position
    menuPos = self.mapToGlobal(QtCore.QPoint(colViewport + self.verticalHeader().width(), rowViewport))

    self.menu = EditDataMenu(parent=self, tableModel=self.tableModel, indexAt=indexAt)
    # apply styles to popup window
    if(QSTYLE != None):
      self.menu.setStyle(QSTYLE)
    if(QSTYLESHEET != None):
      self.menu.setStyleSheet(QSTYLESHEET)
    self.menu.popup(menuPos)    

  def currentCellChanged(self, current):
    # keeps tabs on current cell
    self.currentRow, self.currentCol = current.row(), current.column()

  def isNumber(self, s):
    # checks whether string is a number
    try:
      float(s)
      return True
    except ValueError:
      pass
   
    try:
      import unicodedata
      unicodedata.numeric(s)
      return True
    except (TypeError, ValueError):
      pass
    
    return False

# subclass edit to better capture key presses
class EditDataEdit(QtWidgets.QLineEdit):
  def __init__(self, parent=None):
    super(EditDataEdit, self).__init__(parent)
    self.parent = parent
  
  def keyPressEvent(self, event):
    # ignore alt keys as they would close the QMenu
    if(event.key() in [QtCore.Qt.Key_Alt, QtCore.Qt.Key_AltGr]):
      return

    # capture enter and arrow keys
    if(event.key() in [QtCore.Qt.Key_Return, QtCore.Qt.Key_Enter]):
      if(event.modifiers() & QtCore.Qt.ShiftModifier):
        self.parent.advanceCell(-1, 0)
      else:
        self.parent.advanceCell(1, 0)
    elif(event.key() == QtCore.Qt.Key_Up):
      self.parent.advanceCell(-1, 0)
    elif(event.key() == QtCore.Qt.Key_Down):
      self.parent.advanceCell(1, 0)
    elif(event.key() == QtCore.Qt.Key_Left):
      if((event.modifiers() & QtCore.Qt.ControlModifier) or (self.cursorPosition() == 0)):
        self.parent.advanceCell(0, -1)
        return
    elif(event.key() == QtCore.Qt.Key_Right):
      if((event.modifiers() & QtCore.Qt.ControlModifier) or (self.cursorPosition() == len(self.text()))):
        self.parent.advanceCell(0, 1)
        return
      
    # normal event processing
    QtWidgets.QLineEdit.keyPressEvent(self, event)

class EditDataMenu(KuhMenu):
  def __init__(self, parent=None, tableModel=None, indexAt=None, initialEdit=''):
    super(EditDataMenu, self).__init__()
    if(None in [parent, tableModel, indexAt]):
      self.close()
    
    self.parent = parent
    self.tableModel = tableModel
    self.maxRow, self.maxCol = self.tableModel.rowCount(), self.tableModel.columnCount()
    self.indexAt = indexAt
    self.row, self.col = self.indexAt.row(), self.indexAt.column()
    self.minWidth = scaledDPI(100)
      
    # set up GUI
    self.buildRessource()
    
    # set QMenu position
    self.adjustWindowPosition(initialEdit=initialEdit)

  def adjustWindowPosition(self, initialEdit=''):
    # update label
    labelText = 'Edit cell ' + str(self.col + 1) + '/' + str(self.row + 1)
    self.editDataLabel.setText("<html><head/><body><span style=\"font-size:130%; font-weight:bold;\">" + labelText + "</span></body></html>")

    # update QlineEdit
    if(len(initialEdit)):
      self.initValue = ''
      self.editData.setText(initialEdit)
    else:
      self.initValue = self.tableModel.dataByIndices(self.row, self.col)
      self.editData.setText(str(self.initValue))

    self.editData.selectAll()
    self.editData.setFocus()

    # ensure that cell is visible
    cellIndex = self.tableModel.index(self.row, self.col)
    self.parent.scrollTo(cellIndex)
    
    # adjust width of edit window -- use min/max size as resize not properly heeded
    cellWidth = max(self.minWidth, self.parent.columnWidth(self.col))
    self.editData.setMaximumSize(QtCore.QSize(cellWidth, scaledDPI(BASE_SIZE)))
    self.editData.setMinimumSize(QtCore.QSize(cellWidth, scaledDPI(BASE_SIZE)))
    self.setMaximumWidth(cellWidth)
    self.setMinimumWidth(cellWidth)

    # adjusts window position to currently edited cell
    rowViewport = self.parent.rowViewportPosition(self.row)
    colViewport = self.parent.columnViewportPosition(self.col) + self.parent.verticalHeader().width()
    menuPos = self.parent.mapToGlobal(QtCore.QPoint(colViewport, rowViewport))
    self.move(menuPos)
    
    if(len(initialEdit)):
      self.editData.deselect()
      self.editData.setCursorPosition(1)

  def buildRessource(self):
    # build gui
    self.vLayout = QtWidgets.QVBoxLayout(self)
    self.vLayout.setContentsMargins(0, 0, 0, 0)
    
    # QlineEdit for data modification
    self.editDataLabel = QtWidgets.QLabel()
    self.vLayout.addWidget(self.editDataLabel)
    
    self.editData = EditDataEdit(self)
    self.vLayout.addWidget(self.editData)
    self.editData.setFocus()
    
  def updateData(self):
    # updates data table if required
    currValue = self.editData.text()
    if(currValue != self.initValue):
      try:
        currValue = float(currValue)
      except:
        pass
      self.parent.tableModel.setData(currValue, self.row, self.col)

      # refresh table view
      cellIndex = self.tableModel.index(self.row, self.col)
      self.tableModel.dataChanged.emit(cellIndex, cellIndex, [QtCore.Qt.DisplayRole])
      
  def keyPressEvent(self, event):
    # process tab keys and escape
    if(event.key() == QtCore.Qt.Key_Backtab):
      self.advanceCell(0, -1)
    elif(event.key() == QtCore.Qt.Key_Tab):
      self.advanceCell(0, 1)
    elif(event.key() == QtCore.Qt.Key_Escape):
      self.close()
      
  def advanceCell(self, deltaRow=0, deltaCol=0):
    # update previous data
    self.updateData()
    
    # move edit window to new position
    # adjust cell indices
    self.deltaRow, self.deltaCol = deltaRow, deltaCol
    
    # apply column shift
    self.col += self.deltaCol
    if(self.col >= self.maxCol):
      if(self.row < self.maxRow - 1):
        self.col = 0; self.row += 1
      else:
        self.col = self.maxCol - 1
    elif(self.col < 0):
      if(self.row > 0):
        self.col = self.maxCol - 1; self.row -= 1
      else:
        self.col = 0

    # apply row shift
    self.row += deltaRow
    self.row = max(self.row, 0)
    self.row = min(self.row, self.maxRow - 1)

    # set cursor in data table to currently edited cell
    self.parent.currentCol, self.parent.currentRow = self.col, self.row
    self.parent.clearSelection()
    self.parent.selectTo(self.row, self.row)
    nuIndex = self.parent.model().index(self.row, self.col)
    self.parent.selectionModel().setCurrentIndex(nuIndex, QtCore.QItemSelectionModel.Select)

    # move window
    self.adjustWindowPosition()
    
  def closeEvent(self, event):
    # perform final update
    self.updateData()
    # perform original close event
    QtWidgets.QMenu.closeEvent(self, event)

class ResultsArea(QWidgetMac):
  def __init__(self, parent = None):
    super(ResultsArea, self).__init__()
    self.parent = parent
    self.rolestr = {'x':'x', 'y':'y', 'xerr':u'\N{GREEK CAPITAL LETTER DELTA}x', \
      'yerr':u'\N{GREEK CAPITAL LETTER DELTA}y', 'fit':'fit', 'resid':'resid'}
    self.descriptors = []
    self.buildRessource()
    
  def buildRessource(self):
    # set up results table
    self.vLayout = QtWidgets.QVBoxLayout(self)
    self.vLayout.setContentsMargins(0, 0, 0, 0)
    self.resultstable = QtWidgets.QTableView()
    self.resultstable.setEditTriggers(QtWidgets.QAbstractItemView.NoEditTriggers)
    self.resultstable.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectRows)
    self.vLayout.addWidget(self.resultstable)
    self.tableModel = None

    self.rowHeight = int(self.resultstable.fontMetrics().height() + scaledDPI(2))
    vheader = self.resultstable.verticalHeader()
    vheader.setDefaultSectionSize(self.rowHeight)
    vheader.setSectionResizeMode(QtWidgets.QHeaderView.Fixed)

    self.exportButton = QPushButtonMac()
    self.exportButton.setText('Export Results')
    self.exportButton.setMaximumSize(QtCore.QSize(scaledDPI(100), scaledDPI(BASE_SIZE)))
    self.exportButton.setMinimumSize(QtCore.QSize(scaledDPI(100), scaledDPI(BASE_SIZE)))
    self.exportButton.clicked.connect(self.exportWrapper)
    self.vLayout.addWidget(self.exportButton)

  def exportWrapper(self):
    # writes results to output file
    global REMEMBERDIR
    filter_options = ['HTML Files (*.html)','Excel Files (*.xlsx)']
    filterstring = ';;'.join(filter_options)
    filename, filter_ = QtWidgets.QFileDialog.getSaveFileName(self, filter=filterstring, directory=REMEMBERDIR, caption='Export Results')
    filename = str(filename)
    if(PATH_SEPARATOR in filename):
      REMEMBERDIR = filename.split(PATH_SEPARATOR)[:-1]
      REMEMBERDIR = PATH_SEPARATOR.join(REMEMBERDIR)
    elif('/' in filename):
      REMEMBERDIR = filename.split('/')[:-1]
      REMEMBERDIR = PATH_SEPARATOR.join(REMEMBERDIR)
    if(len(filename) > 0):
      mode = filter_options.index(filter_)
      if(mode == 0):
        self.writeHTML(filename=filename)
      elif(mode == 1):
        self.writeXLS(filename=filename)

  def writeHTML(self, filename=None):
    # writes Results table to HTML file
    if(filename != None):
      # save current figure temporarily under new filename
      try:
        self.parent.plotArea.matplot.savefig(filename, format = 'svg', dpi = 600, facecolor = self.parent.plotArea.figureColor)
        flag = True
      except:
        flag = False
      # store contents of SVG file in memory
      if(flag):
        readhandle = open(filename, 'r')
        svg_plot = readhandle.readlines()
        readhandle.close()
      else:
        svg_plot = []
      
      # save current residuals temporarily under new filename
      try:
        self.parent.plotArea.residplot.savefig(filename, format = 'svg', dpi = 600, facecolor = self.parent.plotArea.figureColor)
        flag2 = True
      except:
        flag2 = False

      # store contents of SVG file in memory
      if(flag2):
        readhandle = open(filename, 'r')
        svg_resid = readhandle.readlines()
        readhandle.close()
      else:
        svg_resid = []
        
      # generate actual HTML file
      writehandle = open(filename, 'w', encoding='utf-8')
      
      if(writehandle):
        # write header
        writehandle.write('<html xmlns="http://www.w3.org/1999/xhtml">\n<head>\n')
        writehandle.write('<title>Fit-o-mat Results</title>\n')
        writehandle.write('<meta charset="UTF-8">\n')
        writehandle.write('<meta author="Moeglich laboratory, University of Bayreuth">\n')
        writehandle.write('<meta description="Fit-o-mat Fit Results">\n')
        writehandle.write('</head>\n<body>\n')
        
        writehandle.write('<h2>Fit-o-mat Results</h2>\n')
        # check whether current fit results are available
        if('fval' in self.descriptors):
          fitresults = self.parent.fitarea.outstring.splitlines()
          for index, entry in enumerate(fitresults[2:]):
            writehandle.write(entry + '<br>\n')
        else:
          pass
            
        writehandle.write('<div class="container">\n')

        # write data
        if((self.tableModel != None) and (self.tableModel.columnCount() > 0)):
          writehandle.write('<div class="flexmatic">\n')
          writehandle.write('<h3>Data and Fitted Values</h3>\n')
          writehandle.write('<table>\n<thead>\n<tr>\n')
          for header in self.tableModel.getHeaders():
            writehandle.write('<th>' + str(header) + '</th>\n')
          writehandle.write('</tr>\n</thead>\n')
          # write data table
          writehandle.write('<tbody>\n')
          resultsData = self.tableModel.getAllData()
          for row in resultsData:
            writehandle.write('<tr>\n')
            row = [self.parent.formatNumber(i) for i in row]
            rowstring = '</td><td>'.join(row)
            writehandle.write('<td>' + rowstring + '</td>')
            writehandle.write('\n</tr>\n')

          writehandle.write('</tbody>\n</table>\n')
          writehandle.write('</div>\n')

        # write simulated data as well
        simX, simY = self.parent.fit[self.parent.activeFit].x, self.parent.fit[self.parent.activeFit].y
        writehandle.write('<div class="flexmatic">\n')
        writehandle.write('<h3>Simulated Curve</h3>\n')
        writehandle.write('<table>\n<thead>\n<tr>\n')
        writehandle.write('<th>x</th>\n<th>f(x)</th>\n')
        writehandle.write('<tbody>\n')
        for row in range(len(simX)):
          writehandle.write('<tr>\n')
          writehandle.write('<td>' + self.parent.formatNumber(simX[row]) + '</td>')
          writehandle.write('<td>' + self.parent.formatNumber(simY[row]) + '</td>')
          writehandle.write('\n</tr>\n')
        writehandle.write('</tbody>\n</table>\n')
        writehandle.write('</div>\n')

        # write graphics
        writehandle.write('<div class="flexmatic2">\n')
        writehandle.write('<h3>Plot and Residuals</h3>\n')
        max_width = 0

        # write plot figure if available
        if(flag):
          output = False
          for entry in svg_plot:
            if('<svg' in entry):
              output = True
              # extract width of SVG item
              if('width' in entry):
                red = entry.split('width')[1]
                max_width = red.split('"')[1]
            if(output):
              writehandle.write(entry)
            if('</svg' in entry):
              output = False
            
        # write residuals figure if available
        if(flag2):
          output = False
          for entry in svg_resid:
            if('<svg' in entry):
              output = True
            if(output):
              writehandle.write(entry)
            if('</svg' in entry):
              output = False

        writehandle.write('</div>\n')
        writehandle.write('</div>\n')
        writehandle.write('<div class="disclaimer">brought to you by AM lab</div>\n')
        # add style definitions
        writehandle.write('</body>\n')
        writehandle.write('<style type="text/css">\n')
        writehandle.write('.container {\npadding: 0;\nmargin: 0;\ndisplay: flex;\nflex-direction: row;\
          \nalign-items: flex-start;\n}\n')
        writehandle.write('.flexmatic {\npadding: 5px;\nmargin: 0;\nflex: 0 0 auto;\n}\n')
        writehandle.write('.flexmatic2 {\npadding: 5px;\nmargin: 0;\nflex: 1 1 auto;\n')
        if(max_width != 0):
          writehandle.write('max-width: ' + max_width + ';\n')
        writehandle.write('min-width: 200pt;\n}\n')
        writehandle.write('svg {\nwidth: 100%;\nheight: 100%;\n}\n')
        writehandle.write('h3 {\ntext-align: center;\n white-space: nowrap;\n}\n')
        writehandle.write('.disclaimer {\nposition: fixed;\nbottom: 0px;\nright: 0px;\nfont-size: 125%;\
                                        color: #333333;\nbackground-color: rgba(255, 255, 255, 0.5);\n\
                                        border: 1px;\nborder-style: solid;\nborder-radius: 2px;\n\
                                        border-color: #333333;\npadding: 2px 10px 2px 10px;\n}\n')
        writehandle.write('</style>\n')
        writehandle.write('</html>\n')
        writehandle.close()
      
  def writeXLS(self, filename=None):
    # writes Results table to Excel file
    if(filename != None):
      try:
        workbook = xlsxwriter.Workbook(filename)
        worksheet = workbook.add_worksheet()
      except:
        self.parent.statusbar.showMessage('Cannot write file ' + filename, self.parent.STATUS_TIME)
      else:
        # check whether current fit results are available
        index = 0
        if('fval' in self.descriptors):
          fitresults = self.parent.fitarea.outstring.splitlines()
          for index, entry in enumerate(fitresults):
            worksheet.write(index, 0, entry)
        offset = index + 2
        # write header
        if((self.tableModel != None) and (self.tableModel.columnCount() > 0)):
          resultsHeader = self.tableModel.getHeaders()
          worksheet.write_row(offset, 0, resultsHeader)
          # write data
          resultsData = self.tableModel.getAllData()
          for rowIndex, row in enumerate(resultsData):
            row = [float(self.parent.formatNumber(i)) if (j != 'labels') else i for i, j in zip(row, resultsHeader)]
            worksheet.write_row(rowIndex + offset + 1, 0, row)
          coloffset = self.tableModel.columnCount() + 1
        else:
          coloffset = 0
        # write simulated data as well
        simX, simY = self.parent.fit[self.parent.activeFit].x, self.parent.fit[self.parent.activeFit].y
        worksheet.write(offset, coloffset, 'x')
        worksheet.write(offset, coloffset + 1, 'f(x)')
        for row in range(len(simX)):
          worksheet.write(row + offset + 1, coloffset, simX[row])
          worksheet.write(row + offset + 1, coloffset + 1, simY[row])
        # write graphics
        chart = workbook.add_chart({'type': 'scatter'})
        worksheet.insert_chart(chr(coloffset+1+67)+str(offset+2), chart)
        # write fit
        chart.add_series({'categories': ['Sheet1', offset+1, coloffset, offset + row + 1, coloffset],\
                          'values': ['Sheet1', offset+1, coloffset + 1, offset + row + 1, coloffset + 1],\
                          'line': {'color': 'red'},\
                          'name': 'fit',\
                          'marker': {'type': 'none'}})
        # write data (if present)
        if(('x' in self.descriptors) and ('y' in self.descriptors)):
          xcol = self.descriptors.index('x'); ycol = self.descriptors.index('y')
          rowcount = self.tableModel.rowCount()
          chartdict = {'categories': ['Sheet1', offset+1, xcol, offset + rowcount, xcol],\
                            'values': ['Sheet1', offset+1, ycol, offset + rowcount, ycol],\
                            'name': 'data',\
                            'marker': {'type': 'diamond'}}
          # include x-errors
          if('xerr' in self.descriptors):
            xerrcol = self.descriptors.index('xerr')
            rangestring = 'Sheet1!$' + chr(xerrcol + 65) + '$' + str(offset + 2) + ':$' + chr(xerrcol + 65) + '$' + str(offset + 1 + rowcount)
            chartdict['x_error_bars'] = {'type': 'custom',\
                     'plus_values': rangestring,\
                     'minus_values': rangestring}
          # include y-errors
          if('yerr' in self.descriptors):
            yerrcol = self.descriptors.index('yerr')
            rangestring = 'Sheet1!$' + chr(yerrcol + 65) + '$' + str(offset + 2) + ':$' + chr(yerrcol + 65) + '$' + str(offset + 1 + rowcount)
            chartdict['y_error_bars'] = {'type': 'custom',\
                     'plus_values': rangestring,\
                     'minus_values': rangestring}
          chart.add_series(chartdict)
    
        workbook.close()
    
  def updateResults(self, values=[], descriptors=[], labels=[]):
    # updates results table
    if(len(values)):
      # prepare table
      if(len(labels)):
        descriptors.append('labels')
        values = values.tolist()
        values = [i + [str(j)] for i, j in zip(values, labels)]
      self.descriptors = descriptors
      self.tableModel = TableModel(values, self.resultstable)
      self.resultstable.setModel(self.tableModel)
      self.tableModel.setAllHeaders(self.descriptors)

      # set col width
      self.colWidth = int(self.resultstable.size().width() / 4.5)
      hheader = self.resultstable.horizontalHeader()
      hheader.setDefaultSectionSize(self.colWidth)
    else:
      self.tableModel = None
      nullModel = TableModel([], self.resultstable)
      self.resultstable.setModel(nullModel)

  def keyPressEvent(self, event):
    if event.matches(QtGui.QKeySequence.Copy):
      # prepare output
      selind = self.resultstable.selectionModel().selectedRows()
      selind = sorted([i.row() for i in selind])      
      # get data
      selectedData = self.tableModel.getDataRows(selind)
      output = ''
      for row in selectedData:
        row = [str(i) for i in row]
        output += '\t'.join(row) + '\n'
      
      clipboard = QtWidgets.QApplication.clipboard()
      clipboard.setText(output)
    else:
      QtWidgets.QWidget.keyPressEvent(self, event)

class DataArea(QWidgetMac):
  def __init__(self, parent = None):
    super(DataArea, self).__init__()
    self.parent = parent
    self.errorModel = 0
    self.errorConst = 1.0
    self.errorPercent = 5.0
    self.errorPropagate = True
    self.reductionModel = 0
    self.reductionSkip = 1
    self.reductionAvg = 2
    self.reductionMovAvg = 2
    self.reductionLog = 100
    self.sheetNumber = 1
    self.transposeData = False

    self.buildRessource()
    self.tableWidget.generateEmptyTable(3, 50)
    
    # set up namespace
    # import numpy again
    import numpy as np
    # import common functions from numpy for ease of access
    from numpy import abs, arccos, arcsin, arctan, exp, cos, cosh, log, log2, log10, power, sin, sinh, sqrt, tan, tanh
    self.mySpace = locals()

  def buildRessource(self):
    # set up GUI
    self.validFloat = QtGui.QDoubleValidator()
    self.validInt = QtGui.QIntValidator()
    self.validInt.setBottom(1)

    # set up data table
    self.vLayout = QtWidgets.QVBoxLayout(self)
    self.vLayout.setContentsMargins(0, 0, 0, 0)
    
    self.importBox = QWidgetMac()
    self.vLayout.addWidget(self.importBox)
    self.importLayout = QtWidgets.QHBoxLayout(self.importBox)
    self.importLayout.setContentsMargins(0, 0, 0, 0)
    self.importLayout.setAlignment(QtCore.Qt.AlignLeft)
    
    self.importButton = QPushButtonMac()
    self.importButton.setText('Open File')
    self.importButton.clicked.connect(self.loadData)
    self.importButton.setMaximumSize(scaledDPI(100), scaledDPI(BASE_SIZE))
    self.importButton.setMinimumSize(scaledDPI(100), scaledDPI(BASE_SIZE))
    self.importLayout.addWidget(self.importButton)

    self.killCommaButton = QPushButtonMac()
    self.killCommaButton.setText('Replace Comma')
    self.killCommaButton.clicked.connect(self.killTheComma)
    self.killCommaButton.setMaximumSize(scaledDPI(100), scaledDPI(BASE_SIZE))
    self.killCommaButton.setMinimumSize(scaledDPI(100), scaledDPI(BASE_SIZE))
    self.importLayout.addWidget(self.killCommaButton)

    self.transposeCheck = QtWidgets.QCheckBox()
    self.transposeCheck = QtWidgets.QCheckBox(self.importBox)
    self.transposeCheck.setGeometry(QtCore.QRect(scaledDPI(2), scaledDPI(2), scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.transposeCheck.setChecked(False)
    self.transposeCheck.setText('transpose?')
    self.transposeCheck.stateChanged.connect(self.dataTransposition)
    self.importLayout.addWidget(self.transposeCheck)
    
    self.sheetBox = QWidgetMac()
    self.vLayout.addWidget(self.sheetBox)
    self.sheetLayout = QtWidgets.QHBoxLayout(self.sheetBox)
    self.sheetLayout.setContentsMargins(0, 0, 0, 0)
    self.sheetLayout.setAlignment(QtCore.Qt.AlignLeft)

    self.importSheetLabel = QtWidgets.QLabel('sheet')
    self.importSheetLabel.setMaximumSize(scaledDPI(28), scaledDPI(BASE_SIZE))
    self.importSheetLabel.setMinimumSize(scaledDPI(28), scaledDPI(BASE_SIZE))
    self.sheetLayout.addWidget(self.importSheetLabel)
    self.importSheetLabel.setEnabled(False)
    
    self.importSheetSpinBox = QtWidgets.QSpinBox()
    self.importSheetSpinBox.setMinimum(1)
    self.importSheetSpinBox.setMaximum(self.sheetNumber)
    self.importSheetSpinBox.setValue(1)
    self.importSheetSpinBox.setMinimumSize(scaledDPI(50), scaledDPI(BASE_SIZE))
    self.importSheetSpinBox.setMaximumSize(scaledDPI(50), scaledDPI(BASE_SIZE))
    self.importSheetSpinBox.valueChanged.connect(self.changeSheet)
    self.importSheetSpinBox.setEnabled(False)
    self.sheetLayout.addWidget(self.importSheetSpinBox)
    
    self.importSheetName = QtWidgets.QLabel()
    self.sheetLayout.addWidget(self.importSheetName)
    self.sheetBox.hide()

    self.tableWidget = DataTable(self)
    self.vLayout.addWidget(self.tableWidget)
    
    # set up box for error specification
    blah = self.HLine()
    self.vLayout.addWidget(blah)
    
    self.errorSelectorBox = QWidgetMac()
    self.errorSelectorBox.setContentsMargins(0, 0, 0, 0)
    self.vLayout.addWidget(self.errorSelectorBox)
    self.errorSelectorLayout = QtWidgets.QHBoxLayout(self.errorSelectorBox)
    self.errorSelectorLayout.setContentsMargins(0, 0, 0, 0)
    
    self.errorSelectorLabel = QtWidgets.QLabel('error')
    self.errorSelectorLabel.setMaximumSize(scaledDPI(32), scaledDPI(BASE_SIZE))
    self.errorSelectorLabel.setMinimumSize(scaledDPI(32), scaledDPI(BASE_SIZE))
    self.errorSelectorLayout.addWidget(self.errorSelectorLabel)
    
    self.errorSelectorGroup = QtWidgets.QGroupBox()
    self.errorSelectorGroup.setMinimumHeight(scaledDPI(2 * BASE_SIZE + 8))
    self.errorSelectorGroup.setMaximumHeight(scaledDPI(2 * BASE_SIZE + 8))
    self.errorSelectorLayout.addWidget(self.errorSelectorGroup)

    self.errorGroupLayout = QtWidgets.QHBoxLayout()
    self.errorSelectorGroup.setLayout(self.errorGroupLayout)
    
    self.errorSelectorButtons = []
    self.errorSelectorButtons.append(QtWidgets.QRadioButton(self.errorSelectorGroup))
    self.errorSelectorButtons[-1].setGeometry(QtCore.QRect(scaledDPI(2), scaledDPI(2),\
      scaledDPI(44), scaledDPI(BASE_SIZE)))
    self.errorSelectorButtons[-1].setChecked(False)
    self.errorSelectorButtons[-1].toggled.connect(partial(self.toggleErrorModel, 3))
    self.errorSelectorButtons[-1].setText('none')
    
    self.errorSelectorButtons.append(QtWidgets.QRadioButton(self.errorSelectorGroup))
    self.errorSelectorButtons[-1].setGeometry(QtCore.QRect(scaledDPI(286), scaledDPI(2),\
      scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.errorSelectorButtons[-1].setChecked(True)
    self.errorSelectorButtons[-1].toggled.connect(partial(self.toggleErrorModel, 0))
    self.errorSelectorButtons[-1].setText(u'\N{GREEK CAPITAL LETTER DELTA}y')
    
    self.errorSelectorButtons.append(QtWidgets.QRadioButton(self.errorSelectorGroup))
    self.errorSelectorButtons[-1].setGeometry(QtCore.QRect(scaledDPI(52),\
      scaledDPI(2), scaledDPI(44), scaledDPI(BASE_SIZE)))
    self.errorSelectorButtons[-1].setChecked(False)
    self.errorSelectorButtons[-1].toggled.connect(partial(self.toggleErrorModel, 1))
    self.errorSelectorButtons[-1].setText('const')
    self.errorConstEntry = QLineEditClick(self.errorSelectorGroup)
    self.errorConstEntry.setGeometry(QtCore.QRect(scaledDPI(106),\
      scaledDPI(2), scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.errorConstEntry.setText(str(self.errorConst))
    self.errorConstEntry.setValidator(self.validFloat)
    self.errorConstEntry.editingFinished.connect(partial(self.validateErrorEntry, self.errorConstEntry, 'errorConst'))
    self.errorConstEntry.focusOutEvent = partial(self.lostFocus, self.errorConstEntry, 'errorConst', self.errorConstEntry.focusOutEvent)
    self.errorConstEntry.focusInEvent = partial(self.gainFocus, self.errorSelectorButtons[-1], self.errorConstEntry.focusInEvent)
    
    self.errorSelectorButtons.append(QtWidgets.QRadioButton(self.errorSelectorGroup))
    self.errorSelectorButtons[-1].setGeometry(QtCore.QRect(scaledDPI(172),\
      scaledDPI(2), scaledDPI(42), scaledDPI(BASE_SIZE)))
    self.errorSelectorButtons[-1].setChecked(False)
    self.errorSelectorButtons[-1].toggled.connect(partial(self.toggleErrorModel, 2))
    self.errorSelectorButtons[-1].setText('prop')
    self.errorPercentEntry = QLineEditClick(self.errorSelectorGroup)
    self.errorPercentEntry.setGeometry(QtCore.QRect(scaledDPI(218),\
      scaledDPI(2), scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.errorPercentEntry.setText(str(self.errorPercent))
    self.errorPercentEntry.editingFinished.connect(partial(self.validateErrorEntry, self.errorPercentEntry, 'errorPercent'))
    self.errorPercentEntry.focusOutEvent = partial(self.lostFocus, self.errorPercentEntry, 'errorPercent', self.errorPercentEntry.focusOutEvent)
    self.errorPercentEntry.focusInEvent = partial(self.gainFocus, self.errorSelectorButtons[-1], self.errorPercentEntry.focusInEvent)
    self.errorPercentEntry.setValidator(self.validFloat)
    self.errorPercentLabel = QtWidgets.QLabel(self.errorSelectorGroup)
    self.errorPercentLabel.setGeometry(QtCore.QRect(scaledDPI(262),\
      scaledDPI(2), scaledDPI(18), scaledDPI(BASE_SIZE)))
    self.errorPercentLabel.setText('%')
    
    self.errorPropagateCheck = QtWidgets.QCheckBox(self.errorSelectorGroup)
    self.errorPropagateCheck.setGeometry(QtCore.QRect(scaledDPI(2), scaledDPI(BASE_SIZE + 4), scaledDPI(80), scaledDPI(BASE_SIZE)))
    self.errorPropagateCheck.setChecked(self.errorPropagate)
    self.errorPropagateCheck.setText('propagate?')
    self.errorPropagateCheck.toggled.connect(self.toggleErrorPropagation)

    # set up box for data reduction
    self.dataReductionBox = QWidgetMac()
    self.dataReductionBox.setContentsMargins(0, 0, 0, 0)
    self.vLayout.addWidget(self.dataReductionBox)
    self.dataReductionLayout = QtWidgets.QHBoxLayout(self.dataReductionBox)
    self.dataReductionLayout.setContentsMargins(0, 0, 0, 0)
    
    self.dataReductionLabel = QtWidgets.QLabel('reduce')
    self.dataReductionLabel.setMaximumSize(scaledDPI(32), scaledDPI(BASE_SIZE))
    self.dataReductionLabel.setMinimumSize(scaledDPI(32), scaledDPI(BASE_SIZE))
    self.dataReductionLayout.addWidget(self.dataReductionLabel)
    
    self.dataReductionGroup = QtWidgets.QGroupBox()
    self.dataReductionGroup.setMinimumHeight(scaledDPI(2 * BASE_SIZE + 8))
    self.dataReductionGroup.setMaximumHeight(scaledDPI(2 * BASE_SIZE + 8))
    self.dataReductionLayout.addWidget(self.dataReductionGroup)
    
    self.dataReductionButtons = []
    self.dataReductionButtons.append(QtWidgets.QRadioButton(self.dataReductionGroup))
    self.dataReductionButtons[-1].setGeometry(QtCore.QRect(scaledDPI(2), scaledDPI(2),\
      scaledDPI(44), scaledDPI(BASE_SIZE)))
    self.dataReductionButtons[-1].setChecked(True)
    self.dataReductionButtons[-1].toggled.connect(partial(self.toggleDataReduction, 0))
    self.dataReductionButtons[-1].setText('none')
    
    self.dataReductionButtons.append(QtWidgets.QRadioButton(self.dataReductionGroup))
    self.dataReductionButtons[-1].setGeometry(QtCore.QRect(scaledDPI(52), scaledDPI(2),\
      scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.dataReductionButtons[-1].setChecked(False)
    self.dataReductionButtons[-1].toggled.connect(partial(self.toggleDataReduction, 1))
    self.dataReductionButtons[-1].setText('skip')

    self.dataSkipEntry = QLineEditClick(self.dataReductionGroup)
    self.dataSkipEntry.setGeometry(QtCore.QRect(scaledDPI(106),\
      scaledDPI(2), scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.dataSkipEntry.setText(str(self.reductionSkip))
    self.dataSkipEntry.editingFinished.connect(partial(self.validateReductionEntry, self.dataSkipEntry, 'reductionSkip'))
    self.dataSkipEntry.focusOutEvent = partial(self.lostFocusInt, self.dataSkipEntry, 'reductionSkip', self.dataSkipEntry.focusOutEvent)
    self.dataSkipEntry.focusInEvent = partial(self.gainFocus, self.dataReductionButtons[-1], self.dataSkipEntry.focusInEvent)
    self.dataSkipEntry.setValidator(self.validInt)
    
    self.dataSkipLabel = QtWidgets.QLabel(self.dataReductionGroup)
    self.dataSkipLabel.setGeometry(QtCore.QRect(scaledDPI(150),\
      scaledDPI(2), scaledDPI(15), scaledDPI(BASE_SIZE)))
    self.dataSkipLabel.setText('pts')

    self.dataReductionButtons.append(QtWidgets.QRadioButton(self.dataReductionGroup))
    self.dataReductionButtons[-1].setGeometry(QtCore.QRect(scaledDPI(172), scaledDPI(2),\
      scaledDPI(36), scaledDPI(BASE_SIZE)))
    self.dataReductionButtons[-1].setChecked(False)
    self.dataReductionButtons[-1].toggled.connect(partial(self.toggleDataReduction, 2))
    self.dataReductionButtons[-1].setText('avg')

    self.dataAvgEntry = QLineEditClick(self.dataReductionGroup)
    self.dataAvgEntry.setGeometry(QtCore.QRect(scaledDPI(218),\
      scaledDPI(2), scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.dataAvgEntry.setText(str(self.reductionAvg))
    self.dataAvgEntry.editingFinished.connect(partial(self.validateReductionEntry, self.dataAvgEntry, 'reductionAvg'))
    self.dataAvgEntry.focusOutEvent = partial(self.lostFocusInt, self.dataAvgEntry, 'reductionAvg', self.dataAvgEntry.focusOutEvent)
    self.dataAvgEntry.focusInEvent = partial(self.gainFocus, self.dataReductionButtons[-1], self.dataAvgEntry.focusInEvent)
    self.dataAvgEntry.setValidator(self.validInt)
    
    self.dataAvgLabel = QtWidgets.QLabel(self.dataReductionGroup)
    self.dataAvgLabel.setGeometry(QtCore.QRect(scaledDPI(262),\
      scaledDPI(2), scaledDPI(15), scaledDPI(BASE_SIZE)))
    self.dataAvgLabel.setText('pts')

    self.dataReductionButtons.append(QtWidgets.QRadioButton(self.dataReductionGroup))
    self.dataReductionButtons[-1].setGeometry(QtCore.QRect(scaledDPI(52), scaledDPI(BASE_SIZE + 4),\
      scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.dataReductionButtons[-1].setChecked(False)
    self.dataReductionButtons[-1].toggled.connect(partial(self.toggleDataReduction, 3))
    self.dataReductionButtons[-1].setText('mvavg')

    self.dataMovAvgEntry = QLineEditClick(self.dataReductionGroup)
    self.dataMovAvgEntry.setGeometry(QtCore.QRect(scaledDPI(106),\
      scaledDPI(BASE_SIZE + 4), scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.dataMovAvgEntry.setText(str(self.reductionMovAvg))
    self.dataMovAvgEntry.editingFinished.connect(partial(self.validateReductionEntry, self.dataMovAvgEntry, 'reductionMovAvg'))
    self.dataMovAvgEntry.focusOutEvent = partial(self.lostFocusInt, self.dataMovAvgEntry, 'reductionMovAvg', self.dataMovAvgEntry.focusOutEvent)
    self.dataMovAvgEntry.focusInEvent = partial(self.gainFocus, self.dataReductionButtons[-1], self.dataMovAvgEntry.focusInEvent)
    self.dataMovAvgEntry.setValidator(self.validInt)
    
    self.dataMovAvgLabel = QtWidgets.QLabel(self.dataReductionGroup)
    self.dataMovAvgLabel.setGeometry(QtCore.QRect(scaledDPI(150),\
      scaledDPI(BASE_SIZE + 4), scaledDPI(15), scaledDPI(BASE_SIZE)))
    self.dataMovAvgLabel.setText('pts')

    self.dataReductionButtons.append(QtWidgets.QRadioButton(self.dataReductionGroup))
    self.dataReductionButtons[-1].setGeometry(QtCore.QRect(scaledDPI(172), scaledDPI(BASE_SIZE + 4),\
      scaledDPI(36), scaledDPI(BASE_SIZE)))
    self.dataReductionButtons[-1].setChecked(False)
    self.dataReductionButtons[-1].toggled.connect(partial(self.toggleDataReduction, 4))
    self.dataReductionButtons[-1].setText('log')

    self.dataLogEntry = QLineEditClick(self.dataReductionGroup)
    self.dataLogEntry.setGeometry(QtCore.QRect(scaledDPI(218),\
      scaledDPI(BASE_SIZE + 4), scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.dataLogEntry.setText(str(self.reductionLog))
    self.dataLogEntry.editingFinished.connect(partial(self.validateReductionEntry, self.dataLogEntry, 'reductionLog'))
    self.dataLogEntry.focusOutEvent = partial(self.lostFocusInt, self.dataLogEntry, 'reductionLog', self.dataLogEntry.focusOutEvent)
    self.dataLogEntry.focusInEvent = partial(self.gainFocus, self.dataReductionButtons[-1], self.dataLogEntry.focusInEvent)
    self.dataLogEntry.setValidator(self.validInt)

    self.dataLogLabel = QtWidgets.QLabel(self.dataReductionGroup)
    self.dataLogLabel.setGeometry(QtCore.QRect(scaledDPI(262),\
      scaledDPI(BASE_SIZE + 4), scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.dataLogLabel.setText('pts (ca.)')

    # set up box for data transform
    self.dataTransformBox = QWidgetMac()
    self.dataTransformBox.setContentsMargins(0, 0, 0, 0)
    self.vLayout.addWidget(self.dataTransformBox)
    self.dataTransformLayout = QtWidgets.QHBoxLayout(self.dataTransformBox)
    self.dataTransformLayout.setContentsMargins(0, 0, 0, 0)
    
    self.dataTransformLabel = QtWidgets.QLabel('transf.')
    self.dataTransformLabel.setMaximumSize(scaledDPI(32), scaledDPI(BASE_SIZE))
    self.dataTransformLabel.setMinimumSize(scaledDPI(32), scaledDPI(BASE_SIZE))
    self.dataTransformLayout.addWidget(self.dataTransformLabel)

    self.dataTransformGroup = QtWidgets.QGroupBox()
    self.dataTransformGroup.setMinimumHeight(scaledDPI(2 * BASE_SIZE + 8))
    self.dataTransformGroup.setMaximumHeight(scaledDPI(2 * BASE_SIZE + 8))
    self.dataTransformLayout.addWidget(self.dataTransformGroup)

    self.dataTransformXCheck = QtWidgets.QCheckBox(self.dataTransformGroup)
    self.dataTransformXCheck.setGeometry(QtCore.QRect(scaledDPI(2),\
      scaledDPI(2), scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.dataTransformXCheck.setChecked(False)
    self.dataTransformXCheck.setText('x =')

    self.dataTransformXEntry = QLineEditClick(self.dataTransformGroup)
    self.dataTransformXEntry.setGeometry(QtCore.QRect(scaledDPI(44),\
      scaledDPI(2), scaledDPI(200), scaledDPI(BASE_SIZE)))
    self.dataTransformXEntry.setText('x')
    self.dataTransformXEntry.textChanged.connect(partial(self.dataTransformXCheck.setChecked, True))

    self.dataTransformYCheck = QtWidgets.QCheckBox(self.dataTransformGroup)
    self.dataTransformYCheck.setGeometry(QtCore.QRect(scaledDPI(2),\
      scaledDPI(BASE_SIZE + 4), scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.dataTransformYCheck.setChecked(False)
    self.dataTransformYCheck.setText('y =')

    self.dataTransformYEntry = QLineEditClick(self.dataTransformGroup)
    self.dataTransformYEntry.setGeometry(QtCore.QRect(scaledDPI(44),\
      scaledDPI(BASE_SIZE + 4), scaledDPI(200), scaledDPI(BASE_SIZE)))
    self.dataTransformYEntry.setText('y')
    self.dataTransformYEntry.textChanged.connect(partial(self.dataTransformYCheck.setChecked, True))

    # set up data import controls
    blah = self.HLine()
    self.vLayout.addWidget(blah)
    
    self.refreshBox = QWidgetMac()
    self.refreshBox.setContentsMargins(0, 0, 0, 0)
    self.vLayout.addWidget(self.refreshBox)
    self.refreshLayout = QtWidgets.QHBoxLayout(self.refreshBox)
    self.refreshLayout.setContentsMargins(0, 0, 0, 0)
    self.refreshButton = QPushButtonMac()
    self.refreshButton.setText('Import Data')
    self.refreshButton.setMaximumHeight(scaledDPI(BASE_SIZE))
    self.refreshButton.setMinimumHeight(scaledDPI(BASE_SIZE))
    self.refreshButton.clicked.connect(partial(self.updateData, False, True, False))
    self.refreshLayout.addWidget(self.refreshButton)

    self.dataSeriesButton = QPushButtonMac()
    self.dataSeriesButton.setText('Import Data Series')
    self.dataSeriesButton.setMaximumHeight(scaledDPI(BASE_SIZE))
    self.dataSeriesButton.setMinimumHeight(scaledDPI(BASE_SIZE))
    self.dataSeriesButton.clicked.connect(self.importDataSeries)
    self.refreshLayout.addWidget(self.dataSeriesButton)
    
    self.refreshCheck = QtWidgets.QCheckBox()
    self.refreshCheck.setText('Auto Import?')
    self.refreshCheck.setChecked(False)
    self.refreshCheck.stateChanged.connect(partial(self.updateData, True, True, False))
    #self.refreshLayout.addWidget(self.refreshCheck)

  def reportState(self):
    # reports data content for saveState function
    retv = self.tableWidget.tableModel.getAllData()
    return retv

  def restoreState(self, data):
    # restores data content from loadState function
    try:
      tableData = ast.literal_eval(data[0])
      self.resetSheetSpinBox(currVal=1, maxVal=1, currName='')
      self.transposeCheck.blockSignals(True)
      self.transposeCheck.setChecked(False)
      self.transposeCheck.blockSignals(False)
      
      self.tableWidget.restoreTable(tableData=tableData)
    except:
      print('Failed to restore data table ' + data[0])

  def killTheComma(self):
    # scour data table for commata and replace them
    self.tableWidget.killTheComma()

  def dataTransposition(self):
    # set data transposition flag
    self.transposeData = self.transposeCheck.isChecked()
    # trigger data transposition
    self.tableWidget.transposeTable()

  def resetSheetSpinBox(self, currVal=1, maxVal=1, currName=''):
    # updates import spin box
    self.importSheetSpinBox.setMaximum(maxVal)
    self.sheetNumber = currVal
    self.importSheetSpinBox.setValue(self.sheetNumber)
    
    if(maxVal > 1):
      self.sheetBox.show()
      self.importSheetSpinBox.setEnabled(True)
      self.importSheetLabel.setEnabled(True)
      self.importSheetName.setText(currName)
    else:
      self.importSheetSpinBox.setEnabled(False)
      self.importSheetLabel.setEnabled(False)
      self.importSheetName.setText('')
      self.sheetBox.hide()

  def changeSheet(self):
    # change current sheet in Excel files with several sheets
    self.sheetNumber = self.importSheetSpinBox.value()
    self.tableWidget.changeSheet(self.sheetNumber, transpose=self.transposeData)

  def gainFocus(self, toggleOption=None, defaultHandler=None, event=None):
    # entry field gained focus
    # select corresponding option
    if(toggleOption != None):
      toggleOption.setChecked(True)

    # pass signal to original handler
    if(defaultHandler != None):
      defaultHandler(event)

  def toggleDataReduction(self, mode=0):
    # change error model
    self.reductionModel = mode

  def toggleErrorModel(self, mode=0):
    # change error model
    self.errorModel = mode

  def toggleErrorPropagation(self):
    # toggles error propagation
    self.errorPropagate = self.errorPropagateCheck.isChecked()

  def lostFocusInt(self, entryobject=None, quantity=None, defaultHandler=None, event=None):
    # entry field lost focus, perform sanity check
    if(entryobject != None):
      entrytext = entryobject.text()
      if(self.parent.isNumber(entrytext)):
        self.__dict__[quantity] = int(entrytext)
      else:
        # restore previous value
        entryobject.setText(str(self.__dict__[quantity]))
    # pass signal to original handler
    if(defaultHandler != None):
      defaultHandler(event)
    
  def validateReductionEntry(self, entryobject=None, quantity=None):
    # validates entryfield
    if(entryobject != None):
      entrytext = entryobject.text()
      if(self.parent.isNumber(entrytext)):
        newnumber = int(entrytext)
        self.__dict__[quantity] = np.abs(newnumber)
      else:
        # restore previous value
        entryobject.setText(str(self.__dict__[quantity]))

  def lostFocus(self, entryobject=None, quantity=None, defaultHandler=None, event=None):
    # entry field lost focus, perform sanity check
    if(entryobject != None):
      entrytext = entryobject.text()
      if(self.parent.isNumber(entrytext)):
        self.__dict__[quantity] = float(entrytext)
      else:
        # restore previous value
        entryobject.setText(str(self.__dict__[quantity]))
    # pass signal to original handler
    if(defaultHandler != None):
      defaultHandler(event)
    
  def validateErrorEntry(self, entryobject=None, quantity=None):
    # validates entryfield
    if(entryobject != None):
      entrytext = entryobject.text()
      if(self.parent.isNumber(entrytext)):
        newnumber = float(entrytext)
        self.__dict__[quantity] = np.abs(newnumber)
        if(newnumber < 0):
          entryobject.setText(str(np.abs(newnumber)))
      else:
        # restore previous value
        entryobject.setText(str(self.__dict__[quantity]))

  def HLine(self):
    # draws a horizontal line
    hline = QtWidgets.QFrame()
    hline.setFrameShape(QtWidgets.QFrame.HLine)
    hline.setFrameShadow(QtWidgets.QFrame.Sunken)
    return hline

  def importDataSeries(self):
    # greedy import of data
    cycleColors = [[0.886, 0.290, 0.2, 1.0], [0.204, 0.541, 0.741, 1.0], [0.596, 0.557, 0.835, 1.0]]
    cycleColors.extend([[0.467, 0.467, 0.467, 1.0], [0.984, 0.757, 0.369, 1.0], [0.557, 0.729, 0.259, 1.0]])
    # check whether any data has been loaded
    if((self.tableWidget.tableModel == None) or (self.tableWidget.tableModel.rowCount() == 0)):
      self.parent.statusbar.showMessage('Open a data file first!', self.parent.STATUS_TIME)
    else:
      # can do this by repeatedly calling updateData
      roles = self.tableWidget.roles
      columnCount = self.tableWidget.tableModel.columnCount()
      
      # check for presence of x and y
      if((not 'x' in roles) or (not 'y' in roles)):
        self.parent.statusbar.showMessage('Assign x and y columns!', self.parent.STATUS_TIME)
      else:
        # remember original y column
        originalY = roles['y']
        
        # change dataset style to line and no symbol
        style = self.parent.data[self.parent.activeData].getStyle()
        if(style['linestyle'] == 'None'):
          self.parent.data[self.parent.activeData].setStyle('linestyle', 'solid', redraw=False)
        if(style['marker'] != 'None'):
          self.parent.data[self.parent.activeData].setStyle('marker', 'None', redraw=False)
        
        # loop over columns
        successes = 0
        currY = originalY
        while((currY < columnCount) and (successes < 100)):
          # check whether current column is already assigned to sth. else
          if((currY == originalY) or (not (currY in list(roles.values())))):
            # update status message as this can take a while
            self.parent.statusbar.showMessage('Now processing column ' + str(currY + 1) + '!', self.parent.STATUS_TIME)
            # set current color
            currColor = (currY - originalY) % len(cycleColors)
            self.parent.data[self.parent.activeData].setStyle('color', cycleColors[currColor], redraw=False)
            # assign new y column
            self.tableWidget.roles['y'] = currY
            # get the new data
            self.updateData(docheck=False, redraw=False, quiet=True)
            # check the new data
            nuData = self.parent.data[self.parent.activeData].value()
            if(('x' in nuData) and (len(nuData['x']))):
              # keep track of successes
              successes += 1
              if((currY + 1 < columnCount) and (successes < 100)):
                # generate a new data set (if needed)
                self.parent.data.append(DataObject(self.parent))
                self.parent.data[-1].setName('Data_' + str(len(self.parent.data)-1))
                # need to copy contents of original object
                self.parent.data[-1].spawned(self.parent.data[self.parent.activeData])
                # set new data object as active
                self.parent.activeData = (len(self.parent.data) - 1)
          currY += 1
        
        # restore original roles
        self.tableWidget.roles['y'] = originalY
        
        # update objects area
        self.parent.objectsarea.refreshDataTable()
        self.parent.objectsarea.refreshResidTable()
        self.parent.objectsarea.refreshCurvesTable()
        self.parent.objectsarea.refreshExtrasTable()
        
        # issue refresh of plots
        self.parent.plotArea.dataplotwidget.myRefresh()
        self.parent.plotArea.residplotwidget.myRefresh()

  def updateData(self, docheck=False, redraw=True, quiet=False):
    # check whether autoimport enabled
    if ((not docheck) or (self.refreshCheck.isChecked())):
      # check whether any data has been loaded
      if((self.tableWidget.tableModel == None) or (self.tableWidget.tableModel.rowCount() == 0)):
        self.parent.statusbar.showMessage('Open a data file first!', self.parent.STATUS_TIME)
      else:
        QtWidgets.QApplication.setOverrideCursor(QtGui.QCursor(QtCore.Qt.WaitCursor))
        QtCore.QCoreApplication.processEvents()
        
        # get and process data
        new_data, roles = self.tableWidget.getData()
        if('labels' in roles):
          # separate numerical data from labels
          labelCol = roles.index('labels')
          labels = [i[labelCol] for i in new_data]
          new_data = [[k for j, k in enumerate(i) if j != labelCol] for i in new_data]
          newRoles = [i for i in roles if i != 'labels']
        else:
          labels = []
          newRoles = roles
        labels = np.array(labels)
        new_data = np.array(new_data)

        # check for presence of x and y
        if((not 'x' in roles) or (not 'y' in roles)):
          if(not quiet):
            self.parent.statusbar.showMessage('Assign x and y columns!', self.parent.STATUS_TIME)
        else:
          # check whether the new selection makes sense
          array_dim = new_data.shape
          if(len(array_dim) == 1):
            if(array_dim[0] > 0):
              if(not quiet):
                self.parent.statusbar.showMessage('Select at least two data rows!', self.parent.STATUS_TIME)
            elif(self.tableWidget.hasComma()):
              if(not quiet):
                self.parent.statusbar.showMessage('Select some data to import them -- try replacing comma in data!', self.parent.STATUS_TIME)
            else:
              if(not quiet):
                self.parent.statusbar.showMessage('Select some data to import them!', self.parent.STATUS_TIME)
          elif ((len(array_dim) > 1) and (array_dim[1] > 1)):
            # process the error model
            if(1 <= self.errorModel <= 2):
              if(self.errorModel == 1):
                # use const
                errors = [self.errorConst] * array_dim[0]
                errors = np.array(errors)
              elif(self.errorModel ==2):
                # use percentage of y
                if('y' in newRoles):
                  index = newRoles.index('y')
                  errors = [self.errorPercent/100.0 * i for i in new_data[:,index]]
                  errors = np.array(errors)
                  #errors = errors.transpose()
                else:
                  if(not quiet):
                    self.parent.statusbar.showMessage('Cannot locate y values for percentage error calculation!', self.parent.STATUS_TIME)
                  
              # check if y-error column already exists
              if('yerr' in newRoles):
                index = newRoles.index('yerr')
                new_data[:,index] = errors
              else:
                newRoles.append('yerr')
                # repackage errors to enable hstacking
                errors = [[i] for i in errors]
                errors = np.array(errors)
                new_data = np.hstack((new_data, errors))
            elif(self.errorModel == 3):
              # no errors => possibly delete yerr column
              if('yerr' in newRoles):
                index = newRoles.index('yerr')
                newRoles.pop(index)
                new_data = np.delete(new_data, index, 1)
              
            # process the data reduction model
            if(self.reductionModel != 0):
              if(self.reductionModel == 1):
                # skip data points by numpy slicing
                new_data = new_data[::self.reductionSkip + 1]
                if('labels' in roles):
                  labels = labels[::self.reductionSkip + 1]
              elif(self.reductionModel == 2):
                # average with error propagation
                if('labels' in roles):
                  new_data, labels = self.movingAverage(sourceData=new_data, roles=newRoles, average=self.reductionAvg, stepsize=self.reductionAvg, labels=labels)
                else:
                  new_data = self.movingAverage(sourceData=new_data, roles=newRoles, average=self.reductionAvg, stepsize=self.reductionAvg)
              elif(self.reductionModel == 3):
                # moving average with error propagation
                if('labels' in roles):
                  new_data, labels = self.movingAverage(sourceData=new_data, roles=newRoles, average=self.reductionMovAvg, stepsize=1, labels=labels)
                else:
                  new_data = self.movingAverage(sourceData=new_data, roles=newRoles, average=self.reductionMovAvg, stepsize=1)
              elif(self.reductionModel == 4):
                # logarithmic data reduction
                if('labels' in roles):
                  new_data, labels = self.logAverage(sourceData=new_data, roles=newRoles, targetpoints=self.reductionLog, labels=labels)
                else:
                  new_data = self.logAverage(sourceData=new_data, roles=newRoles, targetpoints=self.reductionLog)
                
            # do data transform if necessary
            # make copy of original data in case we also have to transform y axis
            if(self.dataTransformYCheck.isChecked()):
              new_data2 = copy.deepcopy(new_data)
            if(self.dataTransformXCheck.isChecked()):
              formula = str(self.dataTransformXEntry.text())
              if(len(formula) > 0):
                # transformer
                formula = 'x = ' + formula
                new_data = self.transformer(sourceData=new_data, roles=newRoles, formula=formula, axis='x')
              else:
                if(not quiet):
                  self.parent.statusbar.showMessage('Enter formula for x transformation!', self.parent.STATUS_TIME)
                
            if(self.dataTransformYCheck.isChecked()):
              formula = str(self.dataTransformYEntry.text())
              if(len(formula) > 0):
                # transformer
                formula = 'y = ' + formula
                new_data2 = self.transformer(sourceData=new_data2, roles=newRoles, formula=formula, axis='y')
                # replace y and yerr columns in new_data
                ycol = newRoles.index('y')
                new_data[:,ycol] = new_data2[:,ycol]
                # do error propagation?
                if(('yerr' in newRoles) and self.errorPropagate):
                  yerrcol = newRoles.index('yerr')
                  new_data[:,yerrcol] = new_data2[:,yerrcol]
              else:
                if(not quiet):
                  self.parent.statusbar.showMessage('Enter formula for y transformation!', self.parent.STATUS_TIME)
                
            # delete all rows with non-numerical content
            for role in newRoles:
              index = newRoles.index(role)
              if('labels' in roles):
                labels = labels[np.isfinite(new_data[:,index])]
              new_data = new_data[np.isfinite(new_data[:,index])]
  
            # assign new data
            if('labels' in roles):
              labels = list(labels)
              self.parent.data[self.parent.activeData].setData(new_data, newRoles, labels=labels)
            else:
              self.parent.data[self.parent.activeData].setData(new_data, newRoles)
              
            # here we should update the plot
            self.parent.data[self.parent.activeData].handleData, self.parent.data[self.parent.activeData].handleErr,\
              self.parent.data[self.parent.activeData].handleBar, self.parent.data[self.parent.activeData].handleStack= \
              self.parent.plotArea.plotData(self.parent.data[self.parent.activeData].value(), dataobject = self.parent.data[self.parent.activeData], \
              handleData = self.parent.data[self.parent.activeData].handleData, handleErr = self.parent.data[self.parent.activeData].handleErr,\
              handleBar = self.parent.data[self.parent.activeData].handleBar, handleStack = self.parent.data[self.parent.activeData].handleStack,\
              redraw=False)
            # and we should redraw the fit function to cover new x-range
            self.parent.fit[self.parent.activeFit].handlePlot = self.parent.plotArea.plotFunction(\
              fitobject=self.parent.fit[self.parent.activeFit], x=[], handlePlot=self.parent.fit[self.parent.activeFit].handlePlot,\
              redraw=False)
            # and we should update the legend
            self.updateLegend(redraw=redraw)
            # and we should update the corresponding residuals
            self.parent.data[self.parent.activeData].handleResid, self.parent.plotArea.handleResidZero = self.parent.plotArea.plotResid(\
              dataobject = self.parent.data[self.parent.activeData], handleResid = self.parent.data[self.parent.activeData].handleResid,\
              handleResidZero = self.parent.plotArea.handleResidZero, redraw=False)
            # and we should update the resid plot (as x-axis will most likely have rescaled)
            self.parent.plotArea.setAxisLimits(lower=self.parent.plotArea.minX, upper=self.parent.plotArea.maxX, axis='x',\
              updateLabel=False, target='resid', redraw=False)
            # draw resid line (again) to ensure coverage of entire x range
            self.parent.plotArea.handleResidZero = self.parent.plotArea.plotResidZero(self.parent.plotArea.handleResidZero, redraw=redraw)
            
            # and we should update the results table
            if('labels' in roles):
              self.parent.resultsarea.updateResults(new_data, newRoles, labels=labels)
            else:
              self.parent.resultsarea.updateResults(new_data, newRoles)
          
        QtWidgets.QApplication.restoreOverrideCursor()

  def transformer(self, sourceData=None, roles=None, formula='', axis='x'):
    self.EPSILON = 1e-9
    # does axis transform
    if(axis in ['x', 'y']):
      if(type(sourceData) != type(None)):
        if(axis in roles):
          # try defining transformation function
          try:
            funcstr = 'def transformThis(self, x, y):'
            funcstr += '\n\t' + formula + '\n\treturn ' + axis
            # generate ffunc in local namespace (this is needed for Python3 vs. Python2, bummer)
            namespace = self.mySpace
            exec(funcstr, namespace)
            # now define the new function in the object scope
            setattr(DataArea, 'transformThis', namespace['transformThis'])
          except:
            self.parent.statusbar.showMessage('Error when setting transformation for ' + axis, self.parent.STATUS_TIME)
          else:
            # do the actual transform
            index = roles.index(axis); #val = sourceData[:,index]
            xindex = roles.index('x'); xval = copy.deepcopy(sourceData[:,xindex])
            yindex = roles.index('y'); yval = copy.deepcopy(sourceData[:,yindex])
            try:
              newVal = self.transformThis(xval, yval)
              # now copy transformed data to data matrix
              sourceData[:,index] = newVal
            except:
              self.parent.statusbar.showMessage('Error when calculating transform for ' + axis, self.parent.STATUS_TIME)
            else:
              # deal with data errors
              errname = axis + 'err'
              if(errname in roles):
                errindex = roles.index(errname)
                # numerically determine derivatives in x and y
                # consider x
                if('xerr' in roles):
                  xerrindex = roles.index('xerr'); xerrval = sourceData[:,xerrindex]; xerrval = xerrval ** 2
                  try:
                    xderiv = self.transformThis(xval + self.EPSILON, yval)
                    xderiv = (xderiv - newVal) / self.EPSILON
                    xderiv = xderiv ** 2
                    newErr = xerrval * xderiv
                  except:
                    pass
                else:
                  newErr = np.array([0] * len(newVal))
                
                # consider y
                if('yerr' in roles):
                  yerrindex = roles.index('yerr'); yerrval = sourceData[:,yerrindex]; yerrval = yerrval ** 2
                  try:
                    yderiv = self.transformThis(xval, yval + self.EPSILON)
                    yderiv = (yderiv - newVal) / self.EPSILON
                    yderiv = yderiv ** 2
                    newErr = newErr + (yerrval * yderiv)
                  except:
                    pass
                  
                # calculate root of error
                newErr = newErr ** 0.5
                sourceData[:,errindex] = newErr

    return sourceData

  def logAverage(self, sourceData=None, roles=None, targetpoints=100, labels=np.array([])):
    # reduces data logarithmically to (approx.) target no. of points
    if(type(sourceData) != type(None)):
      if(('x' in roles) and ('y' in roles)):
        # locate x values
        xcol = roles.index('x')
        xval = sourceData[:,xcol]

        # get positive x values
        posXval = xval[xval > 0]
        if(len(posXval) > 0):
          # calculate target x values on log-spaced scale
          logXval = np.linspace(np.log(np.min(posXval)), np.log(np.max(posXval)), targetpoints)
          targetXval = np.exp(logXval)
          targetBoundary = [0]
          targetBoundary.extend([(targetXval[i] + targetXval[i+1])/2 for i in range(len(targetXval)-1)])
          targetBoundary.append(targetXval[-1])

          # cycle through boundary list
          output = np.array([]); avgLabels = []
          for index, entry in enumerate(targetBoundary[:-1]):
            targetRows = sourceData[sourceData[:,xcol] > targetBoundary[index]]
            labelIndex = len(sourceData[sourceData[:,xcol] <= targetBoundary[index]])
            targetRows = targetRows[targetRows[:,xcol] <= targetBoundary[index+1]]
          
            # check current entry
            if(targetRows.size > 0):
              if((len(targetRows.shape) > 1) and (targetRows.shape[0] > 1)):
                # calculate averages
                newRow = []
                for index2, entry2 in enumerate(roles):
                  if(entry2 in ['x', 'y']):
                    # numerically average x and y values
                    newRow.append(np.average(targetRows[:,index2]))
                  elif(entry2 in ['xerr', 'yerr']):
                    errVal = (targetRows[:,index2] / len(targetRows[:,index2])) ** 2
                    errVal = np.sum(errVal) ** 0.5
                    newRow.append(errVal)
                    
                targetRows = np.array(newRow)
                
              if(labels.size):
                avgLabels.append(labels[labelIndex])

              # append current line to output
              if(len(output) > 0):
                output = np.vstack((output, targetRows))
              else:
                output = targetRows
          
          if(labels.size):
            return output, np.array(avgLabels)
          else:
            return output
  
        else:
          self.parent.statusbar.showMessage('No positive x values, cannot do any reduction!', self.parent.STATUS_TIME)
          return sourceData

  def movingAverage(self, sourceData=None, roles=None, average=1, stepsize=1, labels=np.array([])):
    # calculate a moving average with error propagation
    if(type(sourceData) != type(None)):
      if(('x' in roles) and ('y' in roles)):
        # locate x and y values
        xcol = roles.index('x'); ycol = roles.index('y')
        xval = sourceData[:,xcol]
        yval = sourceData[:,ycol]
        # moving average
        avgXval = np.array([np.average(xval[i:i+average]) for i in range(0, len(xval) - average + 1, stepsize)])
        avgYval = np.array([np.average(yval[i:i+average]) for i in range(0, len(yval) - average + 1, stepsize)])
        # check for presence of error values
        if('yerr' in roles):
          # need to do error propagation
          yerrcol = roles.index('yerr')
          yerrval = sourceData[:,yerrcol]
          yerrval = (yerrval / average) ** 2
          # error propagation
          avgYerrval = np.array([np.sum(yerrval[i:i+average]) for i in range(0, len(yerrval) - average + 1, stepsize)])
          avgYerrval = avgYerrval ** 0.5
        elif('xerr' in roles):
          # need to do error propagation
          xerrcol = roles.index('xerr')
          xerrval = sourceData[:,xerrcol] 
          xerrval = (xerrval / average) ** 2
          # error propagation
          avgXerrval = np.array([np.sum(xerrval[i:i+average]) for i in range(len(0, xerrval) - average + 1, stepsize)])
          avgXerrval = avgXerrval ** 0.5
          
        # deal with data labels
        if(labels.size):
          # use label of first data point to be averaged
          avgLabel = np.array([labels[i] for i in range(0, len(xval) - average + 1, stepsize)])

        # now need to assemble columns according to roles
        procData = np.array([])
        for entry in roles:
          # get current column
          if(entry == 'x'):
            addItem = avgXval
          elif(entry == 'y'):
            addItem = avgYval
          elif(entry == 'xerr'):
            addItem = avgXerrval
          elif(entry == 'yerr'):
            addItem = avgYerrval
          
          # assemble output data
          if(procData.size > 0):
            procData = np.vstack((procData, addItem))
          else:
            procData = addItem

        if(labels.size):
          return procData.transpose(), avgLabel
        else:
          return procData.transpose()
        
  def loadData(self):
    global REMEMBERDIR
    filter_options = ['Excel Files (*.xls; *.xlsx)', 'Text Tab Delimited (*.txt)', 'Text Comma separated (*.txt; *.csv)']
    filterstring = ';;'.join(filter_options)
    filename, filter_ = QtWidgets.QFileDialog.getOpenFileName(self, filter=filterstring, directory = REMEMBERDIR, caption='Open Data')
    filename = str(filename)
    if(PATH_SEPARATOR in filename):
      REMEMBERDIR = filename.split(PATH_SEPARATOR)[:-1]
      REMEMBERDIR = PATH_SEPARATOR.join(REMEMBERDIR)
    elif('/' in filename):
      REMEMBERDIR = filename.split('/')[:-1]
      REMEMBERDIR = PATH_SEPARATOR.join(REMEMBERDIR)
    if(len(filename) > 0):
      mode = filter_options.index(filter_)
      if(mode == 0):
        self.tableWidget.loadXLS(filename=filename, transpose=self.transposeData)
      elif(mode == 1):
        self.tableWidget.loadTextFile(filename=filename, delimiter='\t', transpose=self.transposeData)
      elif(mode == 2):
        self.tableWidget.loadTextFile(filename=filename, delimiter=',', transpose=self.transposeData)

  def updateLegend(self, redraw=True):
    # does legend need to be updated?
    value = self.parent.plotArea.legendVisible
    if(value or redraw):
      self.parent.plotArea.setLegend(value=value, redraw=redraw)

class ShrinkoWidget(QWidgetMac):
  def __init__(self, container=None, factor=1.0, offset=0.0):
    super(ShrinkoWidget, self).__init__()
    self.container = container
    self.factor = factor
    self.offset = offset
    
  def sizeHint(self):
    # dynamically resize canvas
    if(self.container != None):
      totalwidth = self.container.size().width()
      totalheight = self.container.size().height()
      width = totalwidth
      height = int(self.factor * totalheight)
      newdim = QtCore.QSize(width, height)
      return newdim
    
  def resizeEvent(self, event):
    # dynamically resize canvas
    totalheight = self.container.size().height()
    sizehint = self.sizeHint()
    # do not just use resize -- need to change geometry as well
    width = sizehint.width()
    height = sizehint.height()
    xoffset = 0
    yoffset = int(self.offset * totalheight)
    self.setGeometry(QtCore.QRect(xoffset, yoffset, width, height))

class MatplotlibCanvas(QWidgetMac):
  def __init__(self, parent=None):
    super(MatplotlibCanvas, self).__init__()
    self.parent = parent
    
    # initialize param values
    self.initParam()

    # set initial matplotlib style
    matplotlib.style.use(self.stylemodel)
    
    # a validator
    self.validFloat = QtGui.QDoubleValidator()
    
    # generate GUI elements
    self.buildRessource()
    
    # initialize plot
    self.initPlot(initialize=True)

  def initParam(self):
    # allow some spacing around data when autoscaling
    self.data_spacer = 0.025
    
    # initialize some values
    self.minX = 0.0; self.maxX = 1.0
    self.minY = 0.0; self.maxY = 1.0
    self.storeCoord = []
    self.minResidY = -0.5; self.maxResidY = 0.5
    self.modeX, self.modeY = 'linear', 'linear'
    self.EPSILON = 1e-6
    self.DATAPOINTS_SIMULATION = 2000
    self.autoScaleX, self.autoScaleY = True, True
    self.labelX = '$x$'
    self.labelY = '$y$'
    self.labelXColor, self.labelYColor = [0.2, 0.2, 0.2, 1.0], [0.2, 0.2, 0.2, 1.0]
    self.labelXSize, self.labelYSize = 14.0, 14.0
    self.labelXPad, self.labelYPad = 4.0, 4.0
    self.labelXPos, self.labelYPos = 0.5, 0.5
    self.labelXAngle, self.labelYAngle = 0.0, 90.0
    self.labelXAlignment, self.labelYAlignment = 'center', 'center'
    self.axisVisible = {'left':True, 'right':True, 'bottom':True, 'top':True}
    self.axisWidth = {'left':1.0, 'right':1.0, 'bottom':1.0, 'top':1.0}
    self.axisStyle = {'left':'solid', 'right':'solid', 'bottom':'solid', 'top':'solid'}
    self.axisDashStyle = {'left':'butt', 'right':'butt', 'bottom':'butt', 'top':'butt'}
    self.axisColor = {'left':[0.2, 0.2, 0.2, 1.0], 'right':[0.2, 0.2, 0.2, 1.0], \
      'bottom':[0.2, 0.2, 0.2, 1.0], 'top':[0.2, 0.2, 0.2, 1.0]}
    self.axisFont = {'x': 'DejaVu Sans', 'y': 'DejaVu Sans'}
    self.tickFont = {'x': 'DejaVu Sans', 'y': 'DejaVu Sans'}
    self.ticksVisible = {'left':True, 'right':True, 'bottom':True, 'top':True}
    self.ticksWidth = {'left':0.5, 'right':0.5, 'bottom':0.5, 'top':0.5}
    self.ticksLength = {'left':5.0, 'right':5.0, 'bottom':5.0, 'top':5.0}
    self.ticksColor = {'left':[0.2, 0.2, 0.2, 1.0], 'right':[0.2, 0.2, 0.2, 1.0], \
      'bottom':[0.2, 0.2, 0.2, 1.0], 'top':[0.2, 0.2, 0.2, 1.0]}
    self.ticksDirection = {'left':'in', 'right':'in', 'bottom':'in', 'top':'in'}
    # not supported by matplotlib (ticks are markers)
    #self.ticksDashStyle = {'left':'butt', 'right':'butt', 'bottom':'butt', 'top':'butt'}
    self.canvasColor = [0.9, 0.9, 0.9, 1.0]
    self.figureColor = [1.0, 1.0, 1.0, 1.0]
    self.ticksX, self.ticksY, self.ticksResidY = [], [], []
    self.ticksXAuto, self.ticksYAuto, self.ticksResidYAuto = True, True, True
    self.ticksXLabel = []
    self.ticksXColor = [0.2, 0.2, 0.2, 1.0]
    self.ticksYColor = [0.2, 0.2, 0.2, 1.0]
    self.ticksXSize, self.ticksYSize = 12.0, 12.0
    self.ticksXAngle, self.ticksYAngle = 0.0, 0.0
    self.gridVisible = {'x':False, 'y':False}
    self.gridWidth = {'x':0.5, 'y':0.5}
    self.gridStyle = {'x':'dotted', 'y':'dotted'}
    self.gridDashStyle = {'x':'butt', 'y':'butt'}
    self.gridColor = {'x':[0.2, 0.2, 0.2, 1.0], 'y':[0.2, 0.2, 0.2, 1.0]}
    self.gridOrder = {'x':'back', 'y':'back'}
    self.exportWidth = 8.0; self.exportHeight = 6.0
    self.padSize = {'left':0.15, 'right':0.95, 'bottom':0.15, 'top':0.95}
    self.visibilityResidLine = True
    self.zorderResidLine = 1
    self.legendVisible = True
    self.legendPlacement = 'best'
    self.legendColor = {'face':[1.0, 1.0, 1.0, 0.5], 'edge':[0.2, 0.2, 0.2, 1.0]}
    self.legendEdgeWidth = 0.5
    self.legendShadow = False
    self.legendLabelColor = [0.0, 0.0, 0.0, 1.0]
    self.legendLabelSize = 14
    self.legendLabelFont = 'DejaVu Sans'
    self.xkcd = False
    self.xkcdScale, self.xkcdLength, self.xkcdRandomness = 1.0, 100.0, 2.0
    self.xkcdStoreFonts = ['DejaVu Sans']
    self.applyPathStroke = False
    self.pathStrokeWidth, self.pathStrokeColor = 2.0, [1.0, 1.0, 1.0, 1.0]
    self.applyPathShadow = False
    self.pathShadowX, self.pathShadowY, self.pathShadowColor, self.pathShadowAlpha = 2, -2, [0.4, 0.4, 0.4, 0.5], 0.5
    self.pathRhoCheck, self.pathRho = True, 0.5
    self.handleArrow = {'x': None, 'y': None}
    self.handleArrowResid = {'x': None, 'y': None}
    self.arrowVisible = {'x': False, 'y': False}
    self.arrowOverhang = {'x': 0.1, 'y': 0.1}
    self.arrowColor = {'x': [0.2, 0.2, 0.2, 1.0], 'y': [0.2, 0.2, 0.2, 1.0]}
    self.arrowFill = {'x': [0.2, 0.2, 0.2, 1.0], 'y': [0.2, 0.2, 0.2, 1.0]}
    self.arrowHeadLength = {'x': 0.05, 'y': 0.05}
    self.arrowHeadWidth = {'x': 0.03, 'y': 0.03}
    self.arrowOffset = {'x': 0.2, 'y': 0.2}
    self.tickLabelData = False
    self.cursorVisible = False
    self.cursor = None
    
    # store information for graphics export as Python script
    self.rememberSetting = {}
    self.rememberSettingResidLine = {}
    
    # generate copies of certain settings for improved drawing control for resid window
    items = 'axisVisible,axisWidth,axisStyle,axisDashStyle,axisColor,labelX,labelY,labelXColor,labelYColor,labelXSize,labelYSize'.split(',')
    items.extend('labelXPad,labelYPad,labelXPos,labelYPos,labelXAlignment,labelYAlignment,labelXAngle,labelYAngle,axisFont'.split(','))
    items.extend('tickFont,ticksVisible,ticksWidth,ticksLength,ticksColor,ticksDirection'.split(','))
    items.extend('ticksXColor,ticksYColor,ticksXSize,ticksYSize,ticksXAngle,ticksYAngle'.split(','))
    items.extend('gridVisible,gridWidth,gridStyle,gridDashStyle,gridColor,gridOrder,padSize'.split(','))
    for entry in items:
      self.__dict__[entry+'_resid'] = copy.deepcopy(self.__dict__[entry])

    if('bmh' in matplotlib.style.available):
      self.stylemodel = 'bmh'
    else:
      self.stylemodel = matplotlib.style.available[0]
        
  def buildRessource(self):
    # set up matplotlib and canvas
    self.hLayout = QtWidgets.QHBoxLayout(self)
    self.hLayout.setContentsMargins(0, 0, 0, 0)
    # controls for y-axis
    self.yControlBox = QWidgetMac(self)
    self.yControlBox.setGeometry(QtCore.QRect(0, 0, scaledDPI(70), scaledDPI(500)))
    self.yControlBox.setMaximumSize(QtCore.QSize(scaledDPI(70), 16777215))
    self.yControlBox.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(200)))

    self.hLayout.addWidget(self.yControlBox)
    self.vLayout = QtWidgets.QVBoxLayout(self.yControlBox)
    self.vLayout.setContentsMargins(0, 0, 0, 0)
    
    # controls for main plot
    self.yControlsPlotContainer = ShrinkoWidget(container=self.yControlBox, factor=0.75, offset=0.0)
    self.vLayout.addWidget(self.yControlsPlotContainer)
    self.LayoutYControlsPlotContainer = QtWidgets.QVBoxLayout(self.yControlsPlotContainer)
    self.LayoutYControlsPlotContainer.setContentsMargins(0, 0, 0, 0)
    
    self.autoScaleBoxY = QWidgetMac(self)
    self.autoScaleBoxY.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.autoScaleBoxY.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.Layout_ScaleBoxY = QtWidgets.QHBoxLayout(self.autoScaleBoxY)
    self.Layout_ScaleBoxY.setContentsMargins(0, 0, 0, 0)
    self.Layout_ScaleBoxY.setAlignment(QtCore.Qt.AlignLeft|QtCore.Qt.AlignTop)
    self.autoScaleLabelY = QtWidgets.QLabel('Auto?')
    self.Layout_ScaleBoxY.addWidget(self.autoScaleLabelY)
    self.autoScaleCheckY = QtWidgets.QCheckBox()
    self.autoScaleCheckY.setChecked(self.autoScaleY)
    self.autoScaleCheckY.stateChanged.connect(partial(self.setAutoScale, 'y'))
    self.Layout_ScaleBoxY.addWidget(self.autoScaleCheckY)
    self.LayoutYControlsPlotContainer.addStretch()
    self.LayoutYControlsPlotContainer.addWidget(self.autoScaleBoxY)
    
    self.upperLimity = QLineEditClick()
    self.upperLimity.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.upperLimity.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.upperLimity.setValidator(self.validFloat)
    self.upperLimity.setText(str(self.parent.formatNumber(self.maxY)))
    self.upperLimity.editingFinished.connect(partial(self.changeAxisLimits, 'y', 'plot', True))
    self.LayoutYControlsPlotContainer.addStretch()
    self.LayoutYControlsPlotContainer.addWidget(self.upperLimity)

    self.modeSelectory = QComboBoxMac()
    self.modeSelectory.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.modeSelectory.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.LayoutYControlsPlotContainer.addStretch()
    self.LayoutYControlsPlotContainer.addWidget(self.modeSelectory)
    self.modeSelectory.addItem('linear')
    self.modeSelectory.addItem('log')
    self.modeSelectory.currentIndexChanged.connect(partial(self.changeAxisMode, 'y', True))
    
    self.lowerLimity = QLineEditClick()
    self.lowerLimity.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.lowerLimity.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.lowerLimity.setValidator(self.validFloat)
    self.lowerLimity.setText(str(self.parent.formatNumber(self.minY)))
    self.lowerLimity.editingFinished.connect(partial(self.changeAxisLimits, 'y', 'plot', True))
    self.LayoutYControlsPlotContainer.addStretch()
    self.LayoutYControlsPlotContainer.addWidget(self.lowerLimity)
    self.LayoutYControlsPlotContainer.addStretch()
    blah = self.HLine()
    self.LayoutYControlsPlotContainer.addWidget(blah)
    
    # controls for resid plot
    self.yControlsResidContainer = ShrinkoWidget(container=self.yControlBox, factor=0.25, offset=0.75)
    self.vLayout.addWidget(self.yControlsResidContainer)
    self.LayoutYControlsResidContainer = QtWidgets.QVBoxLayout(self.yControlsResidContainer)
    self.LayoutYControlsResidContainer.setContentsMargins(0, 0, 0, 0)
    
    self.upperLimitResidy = QLineEditClick()
    self.upperLimitResidy.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.upperLimitResidy.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.upperLimitResidy.setValidator(self.validFloat)
    self.upperLimitResidy.setText(str(self.parent.formatNumber(self.maxResidY)))
    self.upperLimitResidy.editingFinished.connect(partial(self.changeAxisLimits, 'y', 'resid', True))
    self.LayoutYControlsResidContainer.addWidget(self.upperLimitResidy)

    self.lowerLimitResidy = QLineEditClick()
    self.lowerLimitResidy.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.lowerLimitResidy.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.lowerLimitResidy.setValidator(self.validFloat)
    self.lowerLimitResidy.setText(str(self.parent.formatNumber(self.minResidY)))
    self.lowerLimitResidy.editingFinished.connect(partial(self.changeAxisLimits, 'y', 'resid', True))
    self.LayoutYControlsResidContainer.addWidget(self.lowerLimitResidy)

    # little spacer box to align to plots
    self.SpacerBox = QWidgetMac(self)
    self.SpacerBox.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(25)))
    self.SpacerBox.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(25)))
    self.vLayout.addWidget(self.SpacerBox)

    # define the plot for the residuals
    self.residplot = plt.figure()

    # middle box
    self.middleBox = QWidgetMac(self)
    self.hLayout.addWidget(self.middleBox)
    self.hLayout.setContentsMargins(0, 0, 0, 0)
    self.vLayout2 = QtWidgets.QVBoxLayout(self.middleBox)
    self.vLayout2.setContentsMargins(0, 0, 0, 0)

    # container for plot and residuals
    self.plotContainer = QWidgetMac()
    self.LayoutPlotContainer = QtWidgets.QVBoxLayout(self.plotContainer)
    self.LayoutPlotContainer.setContentsMargins(0, 0, 0, 0)
    self.vLayout2.addWidget(self.plotContainer)
    
    # the actual matplotlib canvas
    self.dataContainer = ShrinkoWidget(container=self.plotContainer, factor=0.8, offset=0.0)
    self.LayoutPlotContainer.addWidget(self.dataContainer)
    self.LayoutDataContainer = QtWidgets.QVBoxLayout(self.dataContainer)
    self.LayoutDataContainer.setContentsMargins(0, 0, 0, 0)
    self.matplot = plt.figure()
    self.dataplotwidget = MyFigureCanvas(self.matplot, self, 'plot')
    self.LayoutDataContainer.addWidget(self.dataplotwidget)
 
    # set up canvas for the residuals
    self.residContainer = ShrinkoWidget(container=self.plotContainer, factor=0.2, offset=0.8)
    self.LayoutPlotContainer.addWidget(self.residContainer)
    self.LayoutResidContainer = QtWidgets.QVBoxLayout(self.residContainer)
    self.LayoutResidContainer.setContentsMargins(0, 0, 0, 0)
    self.residplotwidget = MyFigureCanvas(self.residplot, self, 'resid')
    self.LayoutResidContainer.addWidget(self.residplotwidget)
    
    # controls for x-axis
    self.xControlBox = QWidgetMac(self)
    self.xControlBox.setGeometry(QtCore.QRect(0, 0, scaledDPI(500), scaledDPI(BASE_SIZE + 2)))
    self.xControlBox.setMaximumSize(QtCore.QSize(16777215, scaledDPI(BASE_SIZE + 2)))
    self.xControlBox.setMinimumSize(QtCore.QSize(scaledDPI(200), scaledDPI(BASE_SIZE + 2)))
    self.xControlBox.setContentsMargins(0, 0, 0, 0)
    self.vLayout2.addWidget(self.xControlBox)
    self.hLayout2 = QtWidgets.QHBoxLayout(self.xControlBox)
    self.hLayout2.setContentsMargins(0, 0, 0, 0)

    self.autoScaleBoxX = QWidgetMac(self)
    self.autoScaleBoxX.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.autoScaleBoxX.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.hLayout2.addWidget(self.autoScaleBoxX)
    self.Layout_ScaleBoxX = QtWidgets.QHBoxLayout(self.autoScaleBoxX)
    self.Layout_ScaleBoxX.setContentsMargins(0, 0, 0, 0)
    self.Layout_ScaleBoxX.setAlignment(QtCore.Qt.AlignLeft)
    self.autoScaleLabelX = QtWidgets.QLabel('Auto?')
    self.Layout_ScaleBoxX.addWidget(self.autoScaleLabelX)
    self.autoScaleCheckX = QtWidgets.QCheckBox()
    self.autoScaleCheckX.setChecked(self.autoScaleX)
    self.autoScaleCheckX.stateChanged.connect(partial(self.setAutoScale, 'x'))
    self.Layout_ScaleBoxX.addWidget(self.autoScaleCheckX)

    self.lowerLimitx = QLineEditClick()
    self.lowerLimitx.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.lowerLimitx.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.lowerLimitx.setValidator(self.validFloat)
    self.lowerLimitx.setText(str(self.parent.formatNumber(self.minX)))
    self.lowerLimitx.editingFinished.connect(partial(self.changeAxisLimits, 'x', 'plot', True))
    self.hLayout2.addWidget(self.lowerLimitx)

    self.modeSelectorx = QComboBoxMac()
    self.modeSelectorx.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.modeSelectorx.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.hLayout2.addWidget(self.modeSelectorx)
    self.modeSelectorx.addItem('linear')
    self.modeSelectorx.addItem('log')
    self.modeSelectorx.currentIndexChanged.connect(partial(self.changeAxisMode, 'x', True))
    
    self.upperLimitx = QLineEditClick()
    self.upperLimitx.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.upperLimitx.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.upperLimitx.setValidator(self.validFloat)
    self.upperLimitx.setText(str(self.parent.formatNumber(self.maxX)))
    self.upperLimitx.editingFinished.connect(partial(self.changeAxisLimits, 'x', 'plot', True))
    self.hLayout2.addWidget(self.upperLimitx)
    
  def reportState(self):
    # returns current settings for save state function
    reportItems = ['minX', 'maxX', 'minY', 'maxY', 'minResidY', 'maxResidY', 'modeX', 'modeY', 'autoScaleX', 'autoScaleY']
    retv = {}
    
    for entry in reportItems:
      if(hasattr(self, entry)):
        value = getattr(self, entry)
        retv[entry] = value
    
    return retv
  
  def restoreState(self, settings):
    # restores settings from load state function
    for entry in settings:
      if(hasattr(self, entry)):
        self.__dict__[entry] = settings[entry]

    # remember desired axes limits
    orig_minX, orig_maxX = self.minX, self.maxX
    orig_minY, orig_maxY = self.minY, self.maxY
    orig_minResidY, orig_maxResidY = self.minResidY, self.maxResidY
    
    # apply these settings
    # autoscale
    self.autoScaleCheckX.setChecked(self.autoScaleX)
    self.autoScaleCheckY.setChecked(self.autoScaleY)
    
    # axes modes
    index = self.modeSelectorx.findText(self.modeX)
    if(index + 1):
      self.modeSelectorx.blockSignals(True)
      self.modeSelectorx.setCurrentIndex(index)
      self.modeSelectorx.blockSignals(False)
      self.changeAxisMode('x', redraw=False)
    index = self.modeSelectory.findText(self.modeY)
    if(index + 1):
      self.modeSelectory.blockSignals(True)
      self.modeSelectory.setCurrentIndex(index)
      self.modeSelectory.blockSignals(False)
      self.changeAxisMode('y', redraw=False)
    
    # need to counteract resetting of axis ticks when adjusting axis mode
    minX, maxX = self.minX, self.maxX
    minY, maxY = self.minY, self.maxY
    minResidY, maxResidY = self.minResidY, self.maxResidY
    
    # apply tick formatting
    if(self.ticksXAuto):
      self.setAutoTicks(axis='x', redraw=False, target='plot')
      self.setAutoTicks(axis='x', redraw=False, target='resid')
    else:
      ticksXLabel = self.ticksXLabel
      self.setAxisTicks(value=self.ticksX, axis='x', redraw=False, target='plot')
      self.setAxisTicks(value=self.ticksX, axis='x', redraw=False, target='resid')
      # apply axis labels?
      self.ticksXLabel = ticksXLabel
      if(len(self.ticksXLabel)):
        for axisobject in [self.ax, self.ax_resid]:
          axisobject.xaxis.set_ticklabels(self.ticksXLabel)
          #nullLabels = matplotlib.ticker.NullFormatter()
          #axisobject.xaxis.set_minor_formatter(nullLabels)
      
    if(self.ticksYAuto):
      self.setAutoTicks(axis='y', redraw=False, target='plot')
    else:
      self.setAxisTicks(value=self.ticksY, axis='y', redraw=False, target='plot')
      
    if(self.ticksYAuto):
      self.setAutoTicks(axis='resid', redraw=False, target='resid')
    else:
      self.setAxisTicks(value=self.ticksResidY, axis='resid', redraw=False, target='resid')

    # retrieve settings
    self.minX, self.maxX = minX, maxX
    self.minY, self.maxY = minY, maxY
    self.minResidY, self.maxResidY = minResidY, maxResidY
    
    # check wether we can go to original values specified in state
    if(self.modeX == 'linear'):
      self.minX, self.maxX = orig_minX, orig_maxX
    else:
      self.minX, self.maxX = [i if (i > 0) else j for i, j in zip([orig_minX, orig_maxX], [self.minX, self.maxX])]
    if(self.modeY == 'linear'):
      self.minY, self.maxY = orig_minY, orig_maxY
    else:
      self.minY, self.maxY = [i if (i > 0) else j for i, j in zip([orig_minY, orig_maxY], [self.minY, self.maxY])]
    self.minResidY, self.maxResidY = orig_minResidY, orig_maxResidY
        
    # axes limits
    self.setAxisLimits(lower=self.minX, upper=self.maxX, axis='x', updateLabel=True, target='plot', redraw=False)
    self.setAxisLimits(lower=self.minY, upper=self.maxY, axis='y', updateLabel=True, target='plot', redraw=False)
    self.setAxisLimits(lower=self.minResidY, upper=self.maxResidY, axis='y', updateLabel=True, target='resid', redraw=False)

  def setZOrderResidLine(self, zorder=0, redraw=True):
    # updates z order of residuals
    if(self.zorderResidLine != zorder):
      self.zorderResidLine = zorder
      # update plot if necessary
      if(self.handleResidZero != None):
        self.handleResidZero.set_zorder(self.zorderResidLine + self.parent.zOffset)
        self.rememberSettingResidLine['zorder'] = 'set_zorder(' + repr(self.zorderResidLine + self.parent.zOffset) + ')'
        # update plot
        if(redraw):
          self.residplotwidget.myRefresh()

  def setVisibilityResidLine(self, state=True, redraw=True):
    # toggles visibility of residual zero line
    if(self.visibilityResidLine != state):
      self.visibilityResidLine = state
      if(self.handleResidZero != None):
        self.handleResidZero.set_visible(state)
        self.rememberSettingResidLine['visibility'] = 'set_visible(' + repr(state) + ')'
        # update plot
        if(redraw):
          self.residplotwidget.myRefresh()

  def HLine(self):
    # draws a horizontal line
    hline = QtWidgets.QFrame()
    hline.setFrameShape(QtWidgets.QFrame.HLine)
    hline.setFrameShadow(QtWidgets.QFrame.Sunken)
    return hline

  def legendHelper(self, axisobject=None):
    # helper function called by legend formatters
    if(axisobject == None):
      axisobject = self.ax
    
    # build axis legend objects
    items = []
    for entry in self.parent.data:
      if((entry.handleData != None) and (entry.visibility)):
        # manually process escape characters
        name = '\n'.join(entry.name.split('\\n'))
        name = '\t'.join(name.split('\\t'))
        # test for potential Mathttext errors by creating a dummy text label
        tempText = axisobject.text(1, 1, name)
        try:
          tempText._get_layout(self.matplot.canvas.renderer)
        except:
          # some kind of problem with item label
          self.parent.statusbar.showMessage('Problems with data set label ' + name, self.parent.STATUS_TIME)
          name = name.replace('$', '')
        tempText.remove()
        if(not name.startswith('_')):
          items.append([entry.handleData, name, entry.zorder])
    for entry in self.parent.fit:
      if((entry.handlePlot != None) and (entry.visibility)):
        # manually process escape characters
        name = '\n'.join(entry.name.split('\\n'))
        name = '\t'.join(name.split('\\t'))
        # test for potential Mathttext errors by creating a dummy text label
        tempText = axisobject.text(1, 1, name)
        try:
          tempText._get_layout(self.matplot.canvas.renderer)
        except:
          # some kind of problem with item label
          self.parent.statusbar.showMessage('Problems with curve label ' + name, self.parent.STATUS_TIME)
          name = name.replace('$', '')
        tempText.remove()
        if(not name.startswith('_')):
          items.append([entry.handlePlot, name, entry.zorder])
    # order according to zorder
    items = sorted(items, key=lambda k: k[2])
    handles = [i[0] for i in items]
    labels = [i[1] for i in items]
    
    self.legendHandle = axisobject.legend(handles, labels, loc=self.legendPlacement, shadow=self.legendShadow)
    if(self.legendHandle != None):
      # go via frame properties for enhanced controls
      frame = self.legendHandle.get_frame()
      if(frame != None):
        frame.set_linewidth(self.legendEdgeWidth)
        frame.set_edgecolor(self.legendColor['edge'])
        frame.set_facecolor(self.legendColor['face'])
        frame.set_alpha(self.legendColor['face'][-1])
      
      # set text properties
      texts = self.legendHandle.texts
      for entry in texts:
        entry.set_color(self.legendLabelColor)
        entry.set_fontsize(self.legendLabelSize)
        entry.set_fontname(self.legendLabelFont)
        
      # set z-order to display in front (note that aboutLogo is at 1000)
      self.legendHandle.set_zorder(999)
      
      # and now remember all this
      axisname = 'ax'
      self.rememberSetting['legend'] = 'handleLegend = ' + axisname + '.legend(loc=' + repr(self.legendPlacement) + ', shadow=' + repr(self.legendShadow) + ')\n'
      self.rememberSetting['legend'] += 'if(handleLegend != None):\n'
      self.rememberSetting['legend'] += '\tframe = handleLegend.get_frame()\n'
      self.rememberSetting['legend'] += '\tif(frame != None):\n'
      self.rememberSetting['legend'] += '\t\tframe.set_linewidth(' + repr(self.legendEdgeWidth) + ')\n'
      self.rememberSetting['legend'] += '\t\tframe.set_edgecolor(' + repr(self.legendColor['edge']) + ')\n'
      self.rememberSetting['legend'] += '\t\tframe.set_facecolor(' + repr(self.legendColor['face']) + ')\n'
      self.rememberSetting['legend'] += '\t\tframe.set_alpha(' + repr(self.legendColor['face'][-1]) + ')\n'
      self.rememberSetting['legend'] += '\ttexts = handleLegend.texts\n'
      self.rememberSetting['legend'] += '\tfor entry in texts:\n'
      self.rememberSetting['legend'] += '\t\tentry.set_color(' + repr(self.legendLabelColor) + ')\n'
      self.rememberSetting['legend'] += '\t\tentry.set_fontsize(' + repr(self.legendLabelSize) + ')\n'
      self.rememberSetting['legend'] += '\t\tentry.set_fontname(' + repr(self.legendLabelFont) + ')\n'
          
  def setLegendPlacement(self, value='best', redraw=True, target='plot'):
    # sets placement of legend
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(target == 'plot'):
        plotobject = self.dataplotwidget; axisobject = self.ax
      else:
        plotobject = self.residplotwidget; axisobject = self.ax_resid
      
      if(self.legendPlacement == value):
        redraw = False
        
      self.legendPlacement = value
      if(self.legendVisible):
        self.legendHelper(axisobject)
        if(redraw):
          plotobject.myRefresh()

  def setLegendShadow(self, value=False, redraw=True, target='plot'):
    # sets placement of legend
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(target == 'plot'):
        plotobject = self.dataplotwidget; axisobject = self.ax
      else:
        plotobject = self.residplotwidget; axisobject = self.ax_resid
      
      if(self.legendShadow == value):
        redraw = False
        
      self.legendShadow = value
      if(self.legendVisible):
        self.legendHelper(axisobject)
        if(redraw):
          plotobject.myRefresh()

  def setLegend(self, value=True, redraw=True, target='plot'):
    # sets legend
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(target == 'plot'):
        plotobject = self.dataplotwidget; axisobject = self.ax
      else:
        plotobject = self.residplotwidget; axisobject = self.ax_resid
      
      self.legendVisible = value
      if(self.legendVisible):
        self.legendHelper(axisobject)
      else:
        legend = axisobject.legend()
        if(legend != None):
          legend.remove()
        if('legend' in self.rememberSetting):
          del self.rememberSetting['legend']
      
      if(redraw):
        plotobject.myRefresh()

  def setLegendColor(self, value=[0.5, 0.5, 0.5, 0.5], prop='face', redraw=True, target='plot'):
    # sets color of legend
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(target == 'plot'):
        plotobject = self.dataplotwidget; axisobject = self.ax
      else:
        plotobject = self.residplotwidget; axisobject = self.ax_resid
    else:
      prop = 'abort'

    # update color
    if(prop in ['face', 'edge']):
      if(self.legendColor[prop] == value):
        redraw=False
        
      self.legendColor[prop] = value
      if(self.legendVisible):
        self.legendHelper(axisobject)
        if(redraw):
          plotobject.myRefresh()

  def setLegendLabelColor(self, value=[0.5, 0.5, 0.5, 0.5], redraw=True, target='plot'):
    # sets color of legend
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(target == 'plot'):
        plotobject = self.dataplotwidget; axisobject = self.ax
      else:
        plotobject = self.residplotwidget; axisobject = self.ax_resid

      # update color
      if(self.legendLabelColor == value):
        redraw = False
        
      self.legendLabelColor = value
      if(self.legendVisible):
        self.legendHelper(axisobject)
        if(redraw):
          plotobject.myRefresh()

  def setLegendEdgeWidth(self, value=0.5, redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(target == 'plot'):
        plotobject = self.dataplotwidget; axisobject = self.ax
      else:
        plotobject = self.residplotwidget; axisobject = self.ax_resid

      # sets legend edge width
      if(self.legendEdgeWidth == value):
        redraw = False
        
      self.legendEdgeWidth = value
      self.legendHelper(axisobject)
      if(redraw):
        plotobject.myRefresh()

  def setLegendLabelSize(self, value=0.5, redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(target == 'plot'):
        plotobject = self.dataplotwidget; axisobject = self.ax
      else:
        plotobject = self.residplotwidget; axisobject = self.ax_resid

      # sets legend edge width
      if(self.legendLabelSize == value):
        redraw = False
        
      self.legendLabelSize = value
      self.legendHelper(axisobject)
      if(redraw):
        plotobject.myRefresh()

  def setLegendLabelFont(self, value='DejaVu Sans', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(target == 'plot'):
        plotobject = self.dataplotwidget; axisobject = self.ax
      else:
        plotobject = self.residplotwidget; axisobject = self.ax_resid

      # sets legend edge width
      prevFont = self.legendLabelFont
      if(self.legendLabelFont == value):
        redraw = False
        
      self.legendLabelFont = value
      self.legendHelper(axisobject)
      
      # have to capture errors in case a strange font is set
      try:
        if(redraw):
          plotobject.myRefresh()
      except:
        self.parent.statusbar.showMessage('Experiencing problems setting font ' + self.legendLabelFont + ' -- reverting to ' + prevFont, self.parent.STATUS_TIME)

        self.legendLabelFont = prevFont
        self.legendHelper(axisobject)
        # also capture errors with previous font (can happen if selecting two bad fonts in a row)
        try:
          if(redraw):
            plotobject.myRefresh()
        except:
          safeFont = 'DejaVu Sans'
          self.parent.statusbar.showMessage('Also experiencing problems setting font ' + self.legendLabelFont + ' -- reverting to ' + safeFont, self.parent.STATUS_TIME)
          self.legendLabelFont = safeFont
          self.legendHelper(axisobject)

  def setDataAxisTicks(self, dataSet=0, redraw=True, target='plot'):
    # set x ticks to label values
    useData, roles = self.parent.data[dataSet].getData_n_Fit()
    if('x' in roles):
      xcol = roles.index('x')
      xval = list(useData[:, xcol])
      labels = list(self.parent.data[self.parent.activeData].getLabels())
      minLength = np.min((len(xval), len(labels)))
      if(minLength):
        # we have some labels to place
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid

        flag = False
        labels = labels[:minLength]; xval = xval[:minLength]
        
        # first set new ticks
        axisobject.xaxis.set_ticks(xval)
        lower, upper = self.minX, self.maxX
        if(len(xval)):
          # check for empty list
          if(np.min(xval)<np.min((self.minX, self.maxX))):
            flag = True
            lower = np.min(xval)
          if(np.max(xval)>np.max((self.minX, self.maxX))):
            flag = True
            upper = np.max(xval)
          # special treatment for resid plot
          if(target == 'resid'):
            flag = True
            
        # now set new tick labels
        axisobject.xaxis.set_ticklabels(labels)
        #nullLabels = matplotlib.ticker.NullFormatter()
        #formatterName = 'matplotlib.ticker.NullFormatter()'
        #axisobject.xaxis.set_minor_formatter(nullLabels)
        
        # store settings
        self.ticksX = xval
        self.ticksXLabel = labels
        self.ticksXAuto = False
        self.rememberSetting['ax_tickX'] = 'ax.xaxis.set_ticks(' + repr(list(xval)) + ')\n'
        self.rememberSetting['ax_tickX'] += 'ax.xaxis.set_ticklabels(' + repr(list(labels)) + ')\n'
        #self.rememberSetting['ax_tickX'] += 'ax.xaxis.set_minor_formatter(' + formatterName + ')\n'

        # check whether the new ticks necessitate axis rescaling
        if(flag):
          self.setAxisLimits(lower=lower, upper=upper, axis='x', updateLabel=True, target=target, redraw=False)
          if(target == 'plot'):
            # and we should redraw the fit function to cover new x-range
            self.parent.fit[self.parent.activeFit].handlePlot = self.parent.plotArea.plotFunction(\
              fitobject=self.parent.fit[self.parent.activeFit], x=[], handlePlot=self.parent.fit[self.parent.activeFit].handlePlot,\
              redraw=redraw)
          else:
            # and we should update the resid plot (as x-axis will most likely have rescaled)
            self.parent.plotArea.handleResidZero = self.parent.plotArea.plotResidZero(self.parent.plotArea.handleResidZero, redraw=redraw)
        elif(redraw):
          plotobject.myRefresh()
      else:
        self.parent.statusbar.showMessage('Data set ' + str(dataSet) + ' contains no labels!', self.parent.STATUS_TIME)
    else:
      self.parent.statusbar.showMessage('Current data set ' + str(dataSet) + ' is empty!', self.parent.STATUS_TIME)

  def setAutoTicks(self, axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(target == 'plot'):
        plotobject = self.dataplotwidget; axisobject = self.ax
      else:
        plotobject = self.residplotwidget; axisobject = self.ax_resid
    else:
      axis = 'abort'
    # automatically sets axis ticks
    if(axis in ['x', 'y', 'resid']):
      if(axis == 'x'):
        if(self.modeX == 'linear'):
          autoticks = matplotlib.ticker.AutoLocator()
          autolabels = matplotlib.ticker.ScalarFormatter()
        else:
          autoticks = matplotlib.ticker.LogLocator()
          autolabels = matplotlib.ticker.LogFormatterSciNotation()
        axisobject.xaxis.set_major_locator(autoticks)
        #axisobject.xaxis.set_minor_locator(autoticks)
        axisobject.xaxis.set_major_formatter(autolabels)
        #axisobject.xaxis.set_minor_formatter(autolabels)
        self.ticksX = self.getAxisTicks(axis)
        nuticks = self.ticksX
        # clear labels
        self.ticksXLabel = []
        self.ticksXAuto = True
      elif(axis == 'y'):
        if(self.modeY == 'linear'):
          autoticks = matplotlib.ticker.AutoLocator()
          autolabels = matplotlib.ticker.ScalarFormatter()
        else:
          autoticks = matplotlib.ticker.LogLocator()
          autolabels = matplotlib.ticker.LogFormatterSciNotation()
        axisobject.yaxis.set_major_locator(autoticks)
        #axisobject.yaxis.set_minor_locator(autoticks)
        axisobject.yaxis.set_major_formatter(autolabels)
        #axisobject.yaxis.set_minor_formatter(autolabels)
        self.ticksY = self.getAxisTicks(axis)
        nuticks = self.ticksY
        self.ticksYAuto = True
      else:
        autoticks = matplotlib.ticker.AutoLocator()
        autolabels = matplotlib.ticker.ScalarFormatter()
        axisobject.yaxis.set_major_locator(autoticks)
        #axisobject.yaxis.set_minor_locator(autoticks)
        axisobject.yaxis.set_major_formatter(autolabels)
        #axisobject.yaxis.set_minor_formatter(autolabels)
        self.ticksResidY = self.getAxisTicks(axis)
        nuticks = self.ticksResidY
        self.ticksResidYAuto = True
      
      if(redraw):
        plotobject.myRefresh()
      return nuticks

  def setAxisTicks(self, value=np.array([]), axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(target == 'plot'):
        plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
      else:
        plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
    else:
      axis='abort'
    # sets axis ticks
    if(axis in ['x', 'y', 'resid']):
      flag = False
      if(axis == 'x'):
        if(self.modeX == 'linear'):
          autolabels = matplotlib.ticker.ScalarFormatter()
          formatterName = 'matplotlib.ticker.ScalarFormatter()'
        else:
          autolabels = matplotlib.ticker.LogFormatterSciNotation()
          formatterName = 'matplotlib.ticker.LogFormatterSciNotation()'
        axisobject.xaxis.set_major_formatter(autolabels)
        #axisobject.xaxis.set_minor_formatter(autolabels)
        axisobject.xaxis.set_ticks(value)
        self.rememberSetting[axisname + '_tickX'] = axisname + '.xaxis.set_ticks(' + repr(list(value)) + ')\n'
        self.rememberSetting[axisname + '_tickX'] += axisname + '.xaxis.set_major_formatter(' + formatterName + ')\n'
        #self.rememberSetting[axisname + '_tickX'] += axisname + '.xaxis.set_minor_formatter(' + formatterName + ')\n'
        lower, upper = self.minX, self.maxX
        if(len(value)):
          # check for empty list
          if(np.min(value)<np.min((self.minX, self.maxX))):
            flag = True
            lower = np.min(value)
          if(np.max(value)>np.max((self.minX, self.maxX))):
            flag = True
            upper = np.max(value)
          # special treatment for resid plot
          if(target == 'resid'):
            flag = True
        # clear labels
        self.ticksXLabel = []
        self.ticksXAuto = False
      elif(axis == 'y'):
        axisobject.yaxis.set_ticks(value)
        if(self.modeY == 'linear'):
          autolabels = matplotlib.ticker.ScalarFormatter()
          formatterName = 'matplotlib.ticker.ScalarFormatter()'
        else:
          autolabels = matplotlib.ticker.LogFormatterSciNotation()
          formatterName = 'matplotlib.ticker.LogFormatterSciNotation()'
        axisobject.yaxis.set_major_formatter(autolabels)
        #axisobject.yaxis.set_minor_formatter(autolabels)
        self.rememberSetting[axisname + '_tickY'] = axisname + '.yaxis.set_ticks(' + repr(list(value)) + ')\n'
        self.rememberSetting[axisname + '_tickY'] += axisname + '.yaxis.set_major_formatter(' + formatterName + ')\n'
        #self.rememberSetting[axisname + '_tickY'] += axisname + '.yaxis.set_minor_formatter(' + formatterName + ')\n'
        lower, upper = self.minY, self.maxY
        if(len(value)):
          # check for empty list
          if(np.min(value)<np.min((self.minY, self.maxY))):
            flag = True
            lower = np.min(value)
          if(np.max(value)>np.max((self.minY, self.maxY))):
            flag = True
            upper = np.max(value)
        self.ticksYAuto = False
      else:
        axisobject.yaxis.set_ticks(value)
        autolabels = matplotlib.ticker.ScalarFormatter()
        formatterName = 'matplotlib.ticker.ScalarFormatter()'
        axisobject.yaxis.set_major_formatter(autolabels)
        #axisobject.yaxis.set_minor_formatter(autolabels)
        self.rememberSetting[axisname + '_tickY'] = axisname + '.yaxis.set_ticks(' + repr(list(value)) + ')\n'
        self.rememberSetting[axisname + '_tickY'] += axisname + '.yaxis.set_major_formatter(' + formatterName + ')\n'
        #self.rememberSetting[axisname + '_tickY'] += axisname + '.yaxis.set_minor_formatter(' + formatterName + ')\n'
        lower, upper = self.minResidY, self.maxResidY
        if(len(value)):
          # check for empty list
          if(np.min(value)<np.min((self.minResidY, self.maxResidY))):
            flag = True
            lower = np.min(value)
          if(np.max(value)>np.max((self.minResidY, self.maxResidY))):
            flag = True
            upper = np.max(value)
        self.ticksResidYAuto = False
        
      # check whether the new ticks necessitate axis rescaling
      if(flag):
        if((axis == 'y') or (axis == 'resid')):
          self.setAxisLimits(lower = lower, upper = upper, axis = axis, updateLabel = True, target=target, redraw=redraw)
        else:
          self.setAxisLimits(lower = lower, upper = upper, axis = axis, updateLabel = True, target=target, redraw=False)
          if(target == 'plot'):
            # and we should redraw the fit function to cover new x-range
            self.parent.fit[self.parent.activeFit].handlePlot = self.parent.plotArea.plotFunction(\
              fitobject=self.parent.fit[self.parent.activeFit], x=[], handlePlot=self.parent.fit[self.parent.activeFit].handlePlot,\
              redraw=redraw)
          else:
            # and we should update the resid plot (as x-axis will most likely have rescaled)
            self.parent.plotArea.handleResidZero = self.parent.plotArea.plotResidZero(self.parent.plotArea.handleResidZero, redraw=redraw)
      elif(redraw):
        plotobject.myRefresh()

  def getAxisTicks(self, axis='x'):
    # reports back axis ticks
    if(axis in ['x', 'y', 'resid']):
      if(axis == 'x'):
        ticks = self.ax.xaxis.get_ticklocs()
      elif(axis == 'y'):
        ticks = self.ax.yaxis.get_ticklocs()
      else:
        ticks = self.ax_resid.yaxis.get_ticklocs()
      return ticks
    else:
      return []
      
  def setTickLabelAngle(self, value=12.0, axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['x', 'y']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          # sets tick label size
          if(axis == 'x'):
            if(self.ticksXAngle == value):
              redraw = False
            self.ticksXAngle = value
            tickLabels = axisobject.get_xticklabels(which='both')
            tickLabels.append(axisobject.xaxis.get_offset_text())
          elif(axis == 'y'):
            if(self.ticksYAngle == value):
              redraw = False
            self.ticksYAngle = value
            tickLabels = axisobject.get_yticklabels(which='both')
            tickLabels.append(axisobject.yaxis.get_offset_text())
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(axis == 'x'):
            if(self.ticksXAngle_resid == value):
              redraw = False
            self.ticksXAngle_resid = value
            tickLabels = axisobject.get_xticklabels(which='both')
            tickLabels.append(axisobject.xaxis.get_offset_text())
          elif(axis == 'y'):
            if(self.ticksYAngle_resid == value):
              redraw = False
            self.ticksYAngle_resid = value
            tickLabels = axisobject.get_yticklabels(which='both')
            tickLabels.append(axisobject.yaxis.get_offset_text())
        for entry in tickLabels:
          entry.set_rotation(value)
        # remember settings
        tempRememberSetting = 'tickLabels = ' + axisname + '.get_' + axis + 'ticklabels(which=\'both\')\n'
        tempRememberSetting += 'tickLabels.append(' + axisname + '.' + axis + 'axis.get_offset_text())\n'
        tempRememberSetting += 'for entry in tickLabels:\n\tentry.set_rotation(' + repr(value) + ')\n'
        self.rememberSetting[axisname + '_tickAngle' + axis] = tempRememberSetting
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setTickLabelSize(self, value=12.0, axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['x', 'y']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          # sets tick label size
          if(axis == 'x'):
            if(self.ticksXSize == value):
              redraw = False
            self.ticksXSize = value
            tickLabels = axisobject.get_xticklabels(which='both')
            tickLabels.append(axisobject.xaxis.get_offset_text())
          elif(axis == 'y'):
            if(self.ticksYSize == value):
              redraw = False
            self.ticksYSize = value
            tickLabels = axisobject.get_yticklabels(which='both')
            tickLabels.append(axisobject.yaxis.get_offset_text())
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          # sets tick label size
          if(axis == 'x'):
            if(self.ticksXSize_resid == value):
              redraw = False
            self.ticksXSize_resid = value
            tickLabels = axisobject.get_xticklabels(which='both')
            tickLabels.append(axisobject.xaxis.get_offset_text())
          elif(axis == 'y'):
            if(self.ticksYSize_resid == value):
              redraw = False
            self.ticksYSize_resid = value
            tickLabels = axisobject.get_yticklabels(which='both')
            tickLabels.append(axisobject.yaxis.get_offset_text())
        for entry in tickLabels:
          entry.set_fontsize(value)
        # remember settings
        tempRememberSetting = 'tickLabels = ' + axisname + '.get_' + axis + 'ticklabels(which=\'both\')\n'
        tempRememberSetting += 'tickLabels.append(' + axisname + '.' + axis + 'axis.get_offset_text())\n'
        tempRememberSetting += 'for entry in tickLabels:\n\tentry.set_fontsize(' + repr(value) + ')\n'
        self.rememberSetting[axisname + '_tickFontSize' + axis] = tempRememberSetting
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setAxisLabelSize(self, value=12.0, axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis == 'x'):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.labelXSize == value):
            redraw = False
          self.labelXSize = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.labelXSize_resid == value):
            redraw = False
          self.labelXSize_resid = value

        handleAxis = axisobject.xaxis.label
        handleAxis.set_size(value)
      elif(axis == 'y'):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.labelYSize == value):
            redraw = False
          self.labelYSize = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.labelYSize_resid == value):
            redraw = False
          self.labelYSize_resid = value

        handleAxis = axisobject.yaxis.label
        handleAxis.set_size(value)
      # remember settings
      self.rememberSetting[axisname + '_axisLabelSize' + axis] = axisname + '.' + axis + 'axis.label.set_size(' + repr(value) + ')\n'
      # redraw?
      if(redraw):
        plotobject.myRefresh()

  def setAxisLabelPad(self, value=12.0, axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis == 'x'):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.labelXPad == value):
            redraw = False
          self.labelXPad = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.labelXPad_resid == value):
            redraw = False
          self.labelXPad_resid = value

        axisobject.xaxis.labelpad = value
      elif(axis == 'y'):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.labelYPad == value):
            redraw = False
          self.labelYPad = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.labelYPad_resid == value):
            redraw = False
          self.labelYPad_resid = value

        axisobject.yaxis.labelpad = value
      # remember settings
      self.rememberSetting[axisname + '_axisLabelPad' + axis] = axisname + '.' + axis + 'axis.labelpad = ' + repr(value) + '\n'
      # redraw?
      if(redraw):
        plotobject.myRefresh()

  def setAxisLabelPos(self, value=0.5, axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis == 'x'):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.labelXPos == value):
            redraw = False
          self.labelXPos = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.labelXPos_resid == value):
            redraw = False
          self.labelXPos_resid = value

        axisobject.xaxis.label.set_x(value)
      elif(axis == 'y'):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.labelYPos == value):
            redraw = False
          self.labelYPos = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.labelYPos_resid == value):
            redraw = False
          self.labelYPos_resid = value

        axisobject.yaxis.label.set_y(value)
      # remember settings
      self.rememberSetting[axisname + '_axisLabelPos' + axis] = axisname + '.' + axis + 'axis.label.set_' + axis + '(' + repr(value) + ')\n'
      # redraw?
      if(redraw):
        plotobject.myRefresh()

  def setAxisLabelAngle(self, value=0.0, axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis == 'x'):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.labelXAngle == value):
            redraw = False
          self.labelXAngle = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.labelXAngle_resid == value):
            redraw = False
          self.labelXAngle_resid = value

        axisobject.xaxis.label.set_rotation(value)
      elif(axis == 'y'):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.labelYAngle == value):
            redraw = False
          self.labelYAngle = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.labelYAngle_resid == value):
            redraw = False
          self.labelYAngle_resid = value

        axisobject.yaxis.label.set_rotation(value)
      # remember settings
      self.rememberSetting[axisname + '_axisLabelAngle' + axis] = axisname + '.' + axis + 'axis.label.set_rotation(' + repr(value) + ')\n'
      # redraw?
      if(redraw):
        plotobject.myRefresh()

  def setAxisArrow(self, state=True, axis='x', redraw=True, target='plot'):
    # toggles drawing of arrow
    if((target in ['plot', 'resid']) and (axis in ['x', 'y'])):
      if(target == 'plot'):
        plotobject = self.dataplotwidget; arrowhandle = self.handleArrow
      else:
        plotobject = self.residplotwidget; arrowhandle = self.handleArrowResid
      self.arrowVisible[axis] = state
      if(state):
        self.drawAxisArrow(axis=axis, redraw=redraw, target=target)
      elif(arrowhandle[axis] != None):
        arrowhandle[axis].remove()
        arrowhandle[axis] = None
        if(redraw):
          plotobject.myRefresh()        

  def setAxisArrowColor(self, value=[0.0, 0.0, 0.0, 1.0], axis='x', item='fill', redraw=True):
    # changes color axis arrow
    if((axis in ['x', 'y']) and (item in ['line', 'fill'])):
      if(item == 'line'):
        self.arrowColor[axis] = value
      else:
        self.arrowFill[axis] = value
        
      if((redraw) and (self.arrowVisible[axis])):
        self.drawAxisArrow(axis=axis, redraw=redraw, target='plot')
        self.drawAxisArrow(axis=axis, redraw=redraw, target='resid')

  def setAxisArrowHeadWidth(self, value=0.1, axis='x', redraw=True):
    # changes width of axis arrow
    if(axis in ['x', 'y']):
      if(self.arrowHeadWidth[axis] == value):
        redraw = False
      self.arrowHeadWidth[axis] = value

      if((redraw) and (self.arrowVisible[axis])):
        self.drawAxisArrow(axis=axis, redraw=redraw, target='plot')
        self.drawAxisArrow(axis=axis, redraw=redraw, target='resid')

  def setAxisArrowHeadLength(self, value=0.1, axis='x', redraw=True):
    # changes width of axis arrow
    if(axis in ['x', 'y']):
      if(self.arrowHeadLength[axis] == value):
        redraw = False
      self.arrowHeadLength[axis] = value

      if((redraw) and (self.arrowVisible[axis])):
        self.drawAxisArrow(axis=axis, redraw=redraw, target='plot')
        self.drawAxisArrow(axis=axis, redraw=redraw, target='resid')

  def setAxisArrowOverhang(self, value=0.1, axis='x', redraw=True):
    # changes overhang of axis arrow
    if(axis in ['x', 'y']):
      if(self.arrowOverhang[axis] == value):
        redraw = False
      self.arrowOverhang[axis] = value

      if((redraw) and (self.arrowVisible[axis])):
        self.drawAxisArrow(axis=axis, redraw=redraw, target='plot')
        self.drawAxisArrow(axis=axis, redraw=redraw, target='resid')

  def setAxisArrowOffset(self, value=0, axis='x', redraw=True):
    # changes offset of axis arrow
    if(axis in ['x', 'y']):
      if(self.arrowOffset[axis] == value):
        redraw = False
      self.arrowOffset[axis] = value

      if((redraw) and (self.arrowVisible[axis])):
        self.drawAxisArrow(axis=axis, redraw=redraw, target='plot')
        self.drawAxisArrow(axis=axis, redraw=redraw, target='resid')

  def drawAxisArrow(self, axis='x', redraw=True, target='plot'):
    # draws arrowhead along axis
    if((target in ['plot', 'resid']) and (axis in ['x', 'y'])):
      # assign handles
      if(target == 'plot'):
        plotobject = self.dataplotwidget; axisobject = self.ax; arrowhandle = self.handleArrow
      else:
        plotobject = self.residplotwidget; axisobject = self.ax_resid; arrowhandle = self.handleArrowResid

      # assign values
      drawCol = self.arrowColor[axis]
      drawFill = self.arrowFill[axis]
      drawOverhang = self.arrowOverhang[axis]
      drawOffset = self.arrowOffset[axis]
      drawHeadWidth = self.arrowHeadWidth[axis]
      drawHeadLength = self.arrowHeadLength[axis]
      drawZ = axisobject.spines['bottom'].get_zorder() + 0.1
      
      # which axis to operate on?
      if(axis=='x'):
        # calculate drawWidth
        if(self.modeX == 'linear'):
          drawWidth = np.abs(self.maxX - self.minX)
          logx = False
        else:
          drawWidth = np.abs(np.log(self.maxX) - np.log(self.minX))
          logx = True

        drawHeadLength *= drawWidth
  
        # calculate drawHeight
        if(target == 'plot'):
          if(self.modeY == 'linear'):
            drawHeight = np.abs(self.maxY - self.minY)
            logy = False
          else:
            drawHeight = np.abs(np.log(self.maxY) - np.log(self.minY))
            logy = True

          drawHeadWidth *= drawHeight
        else:
          drawHeight = np.abs(self.maxResidY - self.minResidY)
          # resid plot is always linear in y; account for difference in window size
          drawHeadWidth *= drawHeight * 4.0
          logy = False

        # assign line width and xy coordinates
        drawLw = self.axisWidth['bottom']
        drawCs = self.axisDashStyle['bottom']
        
        # apply offset
        if(self.modeX == 'linear'):
          drawX = np.max((self.minX, self.maxX))
        else:
          drawX = np.max((np.log(self.minX), np.log(self.maxX)))
        drawX -= drawOffset * drawHeadLength
        
        # determine drawY
        if(target == 'plot'):
          if(self.modeY == 'linear'):
            drawY = np.min((self.minY, self.maxY))
          else:
            drawY = np.min((np.log(self.minY), np.log(self.maxY)))
        else:
          drawY = np.min((self.minResidY, self.maxResidY))
      else:
        # calculate drawWidth
        if(self.modeX == 'linear'):
          drawHeight = np.abs(self.maxX - self.minX)
          logx = False
        else:
          drawHeight = np.abs(np.log(self.maxX) - np.log(self.minX))
          logx = True

        drawHeadWidth *= drawHeight
  
        # calculate drawHeight
        if(target == 'plot'):
          if(self.modeY == 'linear'):
            drawWidth = np.abs(self.maxY - self.minY)
            logy = False
          else:
            drawWidth = np.abs(np.log(self.maxY) - np.log(self.minY))
            logy = True
          drawHeadLength *= drawWidth
        else:
          drawWidth = np.abs(self.maxResidY - self.minResidY)
          # resid plot is always linear in y; account for difference in window size
          drawHeadLength *= drawWidth * 4.0
          logy = False

        # assign line width and xy coordinates
        drawLw = self.axisWidth['left']
        drawCs = self.axisDashStyle['left']

        # apply offset
        if(target == 'resid'):
          drawY = np.max((self.minResidY, self.maxResidY))
        elif (self.modeY == 'linear'):
          drawY = np.max((self.minY, self.maxY))
        else:
          drawY = np.max((np.log(self.minY), np.log(self.maxY)))
        drawY -= drawOffset * drawHeadLength
        
        # determine drawX
        if(self.modeX == 'linear'):
          drawX = np.min((self.minX, self.maxX))
        else:
          drawX = np.min((np.log(self.minX), np.log(self.maxX)))

      # draw customized arrow
      if(arrowhandle[axis] != None):
        arrowhandle[axis].remove()
      arrowhandle[axis] = self.drawMyArrow(axisobject=axisobject, x=drawX, y=drawY, axis=axis,\
        head_width=drawHeadWidth, head_length=drawHeadLength, overhang=drawOverhang, linewidth=drawLw,\
        linecolor=drawCol, fillcolor=drawFill, capstyle=drawCs, zorder=drawZ, logx=logx, logy=logy)
      arrowhandle[axis].set_clip_on(False)

      if(redraw):
        plotobject.myRefresh()

  def drawMyArrow(self, axisobject, x, y, axis, head_width, head_length, overhang, linewidth, linecolor, fillcolor, capstyle, zorder, logx=False, logy=False):
    # draw customized arrow
    # calculate coordinates
    coords = np.array(4 * [[x, y]])
    if(axis=='x'):
      coords[0, 0] += head_length * overhang
      coords[2, 0] += head_length
      coords[1, 1] += head_width/2.0
      coords[3, 1] -= head_width/2.0
    else:
      coords[1, 0] += head_width/2.0
      coords[3, 0] -= head_width/2.0
      coords[0, 1] += head_length * overhang
      coords[2, 1] += head_length

    # transform to log scale?
    if(logx):
      coords[:, 0] = np.exp(coords[:,0])
    if(logy):
      coords[:, 1] = np.exp(coords[:,1])

    if(axisobject is self.ax):
      axisname = 'ax'
    else:
      axisname = 'ax_resid'
      
    if(overhang < 1):
      polyPatch = matplotlib.patches.Polygon(coords, closed=True, facecolor=fillcolor, fill=True,\
        edgecolor=linecolor, linestyle='solid', linewidth=linewidth, zorder=zorder, capstyle=capstyle)
      retv = axisobject.add_patch(polyPatch)
      self.rememberSetting[axisname + '_arrow' + axis] = 'coords = np.array(' + repr(coords.tolist()) + ')\n'
      self.rememberSetting[axisname + '_arrow' + axis] += 'polyPatch = matplotlib.patches.Polygon(coords, closed=True, facecolor='\
        + repr(fillcolor) + ', fill=True, edgecolor=' + repr(linecolor) + ', linestyle=\'solid\', linewidth='\
        + repr(linewidth) + ', zorder=' + repr(zorder) + ', capstyle=' + repr(capstyle) + ')\n'
      self.rememberSetting[axisname + '_arrow' + axis] += 'patchHandle = ' + axisname + '.add_patch(polyPatch)\n'
      self.rememberSetting[axisname + '_arrow' + axis] += 'patchHandle.set_clip_on(False)\n'
    else:
      polyPatch = matplotlib.patches.Polygon(coords[1:,:], closed=False, fill=False,\
        edgecolor=linecolor, linestyle='solid', linewidth=linewidth, zorder=zorder, capstyle=capstyle)
      retv = axisobject.add_patch(polyPatch)
      self.rememberSetting[axisname + '_arrow' + axis] = 'coords = np.array(' + repr(coords[1:,:].tolist()) + ')\n'
      self.rememberSetting[axisname + '_arrow' + axis] += 'polyPatch = matplotlib.patches.Polygon(coords, closed=False'\
        + ', fill=False, edgecolor=' + repr(linecolor) + ', linestyle=\'solid\', linewidth='\
        + repr(linewidth) + ', zorder=' + repr(zorder) + ', capstyle=' + repr(capstyle) + ')\n'
      self.rememberSetting[axisname + '_arrow' + axis] += 'patchHandle = ' + axisname + '.add_patch(polyPatch)\n'
      self.rememberSetting[axisname + '_arrow' + axis] += 'patchHandle.set_clip_on(False)\n'

    return retv

  def setFigureColor(self, value=[0, 0, 0, 1], redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(target == 'plot'):
        plotobject = self.dataplotwidget; matobject = self.matplot; objectname = 'matplot'
      else:
        plotobject = self.residplotwidget; matobject = self.residplot; objectname = 'residplot'
      # sets figure background color
      if((self.figureColor == value) and (target == 'plot')):
        redraw = False
        
      self.figureColor = value
      matobject.set_facecolor(self.figureColor)
      # remember settings
      self.rememberSetting[objectname + '_figureColor'] = objectname + '.set_facecolor(' + repr(value) + ')\n'
      # redraw?
      if(redraw):
        plotobject.myRefresh()
        
  def setCanvasColor(self, value=[0, 0, 0, 1], redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(target == 'plot'):
        plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
      else:
        plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
      # sets canvas color
      if((self.canvasColor == value) and (target == 'plot')):
        redraw = False

      self.canvasColor = value
      axisobject.patch.set_facecolor(self.canvasColor)
      # remember settings
      self.rememberSetting[axisname + '_canvasColor'] = axisname + '.patch.set_facecolor(' + repr(value) + ')\n'
      # redraw?
      if(redraw):
        plotobject.myRefresh()

  def setGridOrder(self, value='back', axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['x', 'y']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.gridOrder[axis] == value):
            redraw = False
          self.gridOrder[axis] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.gridOrder_resid[axis] == value):
            redraw = False
          self.gridOrder_resid[axis] = value
        # sets grid line style
        if(value == 'back'):
          behind = True
          zorder = 0
        else:
          behind = False
          zorder = 500
        if(axis == 'x'):
          gridlines = axisobject.get_xgridlines()
        else:
          gridlines = axisobject.get_ygridlines()
        for entry in gridlines:
          # matplotlib apparently ignores z order :(
          entry.set_zorder(zorder)
        # use axis setting instead
        axisobject.set_axisbelow(behind)
        # remember settings
        self.rememberSetting[axisname + '_gridOrder' + axis] = 'gridLines = ' + axisname + '.get_' + axis + 'gridlines()\n'
        self.rememberSetting[axisname + '_gridOrder' + axis] += 'for entry in gridLines:\n\tentry.set_zorder(' + repr(zorder) + ')\n'
        self.rememberSetting[axisname + '_gridOrder' + axis] += axisname + '.set_axisbelow(' + repr(behind) + ')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setGridStyle(self, value='solid', axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['x', 'y']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.gridStyle[axis] == value):
            redraw = False
          self.gridStyle[axis] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.gridStyle_resid[axis] == value):
            redraw = False
          self.gridStyle_resid[axis] = value
        # sets grid line style
        if(axis == 'x'):
          gridlines = axisobject.get_xgridlines()
        else:
          gridlines = axisobject.get_ygridlines()
        for entry in gridlines:
          entry.set_linestyle(value)
        # remember settings
        self.rememberSetting[axisname + '_gridStyle' + axis] = 'gridLines = ' + axisname + '.get_' + axis + 'gridlines()\n'
        self.rememberSetting[axisname + '_gridStyle' + axis] += 'for entry in gridLines:\n\tentry.set_linestyle(' + repr(value) + ')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setGridDashStyle(self, value='solid', axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['x', 'y']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.gridDashStyle[axis] == value):
            redraw = False
          self.gridDashStyle[axis] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.gridDashStyle_resid[axis] == value):
            redraw = False
          self.gridDashStyle_resid[axis] = value
        # sets grid line style
        if(axis == 'x'):
          gridlines = axisobject.get_xgridlines()
        else:
          gridlines = axisobject.get_ygridlines()
        for entry in gridlines:
          entry.set_dash_capstyle(value)
          entry.set_solid_capstyle(value)
        # remember settings
        self.rememberSetting[axisname + '_gridDashStyle' + axis] = 'gridLines = ' + axisname + '.get_' + axis + 'gridlines()\n'
        self.rememberSetting[axisname + '_gridDashStyle' + axis] += 'for entry in gridLines:\n\tentry.set_dash_capstyle(' + repr(value) + ')'
        self.rememberSetting[axisname + '_gridDashStyle' + axis] += '\n\tentry.set_solid_capstyle(' + repr(value) + ')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setGridWidth(self, value=0.5, axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['x', 'y']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.gridWidth[axis] == value):
            redraw = False
          self.gridWidth[axis] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.gridWidth_resid[axis] == value):
            redraw = False
          self.gridWidth_resid[axis] = value
        # sets grid line width
        if(axis == 'x'):
          gridlines = axisobject.get_xgridlines()
        else:
          gridlines = axisobject.get_ygridlines()
        for entry in gridlines:
          entry.set_linewidth(value)
        # remember settings
        self.rememberSetting[axisname + '_gridWidth' + axis] = 'gridLines = ' + axisname + '.get_' + axis + 'gridlines()\n'
        self.rememberSetting[axisname + '_gridWidth' + axis] += 'for entry in gridLines:\n\tentry.set_linewidth(' + repr(value) + ')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setGridColor(self, value=[0, 0, 0, 1], axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['x', 'y']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.gridColor[axis] == value):
            redraw = False
          self.gridColor[axis] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.gridColor_resid[axis] == value):
            redraw = False
          self.gridColor_resid[axis] = value
        # sets grid color
        if(axis == 'x'):
          gridlines = axisobject.get_xgridlines()
        else:
          gridlines = axisobject.get_ygridlines()
        for entry in gridlines:
          entry.set_color(value)
        # remember settings
        self.rememberSetting[axisname + '_gridColor' + axis] = 'gridLines = ' + axisname + '.get_' + axis + 'gridlines()\n'
        self.rememberSetting[axisname + '_gridColor' + axis] += 'for entry in gridLines:\n\tentry.set_color(' + repr(value) + ')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setGridVisibility(self, value=True, axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['x', 'y']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.gridVisible[axis] == value):
            redraw = False
          self.gridVisible[axis] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.gridVisible_resid[axis] == value):
            redraw = False
          self.gridVisible_resid[axis] = value

        # sets visibility of grid lines
        if(axis == 'x'):
          gridlines = axisobject.get_xgridlines()
        else:
          gridlines = axisobject.get_ygridlines()
        for entry in gridlines:
          entry.set_visible(value)
        # remember settings
        self.rememberSetting[axisname + '_gridVisibility' + axis] = 'gridLines = ' + axisname + '.get_' + axis + 'gridlines()\n'
        self.rememberSetting[axisname + '_gridVisibility' + axis] += 'for entry in gridLines:\n\tentry.set_visible(' + repr(value) + ')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setPadding(self, value=0.5, axis='bottom', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['bottom', 'top', 'left', 'right']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; matobject = self.matplot; objectname = 'matplot'
          if(self.padSize[axis] == value):
            redraw = False
          self.padSize[axis] = value
        else:
          plotobject = self.residplotwidget; matobject = self.residplot; objectname = 'residplot'
          if(self.padSize_resid[axis] == value):
            redraw = False
          self.padSize_resid[axis] = value
        # sets padding
        matobject.subplots_adjust(left=self.padSize['left'], right=self.padSize['right'],\
          bottom=self.padSize['bottom'], top=self.padSize['top'])
        # remember settings
        self.rememberSetting[objectname + '_padding'] = objectname + '.subplots_adjust(left=' + repr(self.padSize['left'])
        self.rememberSetting[objectname + '_padding'] += ', right=' + repr(self.padSize['right']) + ', bottom=' + repr(self.padSize['bottom'])
        self.rememberSetting[objectname + '_padding'] += ', top=' + repr(self.padSize['top']) + ')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setTickLabelColor(self, value=[0, 0, 0, 1], axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['x', 'y']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          # sets axis label color
          if(axis == 'x'):
            if(self.ticksXColor == value):
              redraw = False
            self.ticksXColor = value
            tickLabels = axisobject.get_xticklabels(which='both')
            tickLabels.append(axisobject.xaxis.get_offset_text())
          else:
            if(self.ticksYColor == value):
              redraw = False
            self.ticksYColor = value
            tickLabels = axisobject.get_yticklabels(which='both')
            tickLabels.append(axisobject.yaxis.get_offset_text())
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          # sets axis label color
          if(axis == 'x'):
            if(self.ticksXColor_resid == value):
              redraw = False
            self.ticksXColor_resid = value
            tickLabels = axisobject.get_xticklabels(which='both')
            tickLabels.append(axisobject.xaxis.get_offset_text())
          else:
            if(self.ticksYColor_resid == value):
              redraw = False
            self.ticksYColor_resid = value
            tickLabels = axisobject.get_yticklabels(which='both')
            tickLabels.append(axisobject.yaxis.get_offset_text())
        for entry in tickLabels:
          entry.set_color(value)
        # remember settings
        tempRememberSetting = 'tickLabels = ' + axisname + '.get_' + axis + 'ticklabels(which=\'both\')\n'
        tempRememberSetting += 'tickLabels.append(' + axisname + '.' + axis + 'axis.get_offset_text())\n'
        tempRememberSetting += 'for entry in tickLabels:\n\tentry.set_color(' + repr(value) + ')\n'
        self.rememberSetting[axisname + '_tickColor' + axis] = tempRememberSetting
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setTickMarkDirection(self, value='in', axis='left', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['left', 'right', 'bottom', 'top']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.ticksDirection[axis] == value):
            redraw = False
          # for time being, left/right and top/bottom are linked
          if (axis in ['left', 'right']):
            axis = 'y'
            self.ticksDirection['left'] = value
            self.ticksDirection['right'] = value
          else:
            axis = 'x'
            self.ticksDirection['top'] = value
            self.ticksDirection['bottom'] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.ticksDirection_resid[axis] == value):
            redraw = False
          # for time being, left/right and top/bottom are linked
          if (axis in ['left', 'right']):
            axis = 'y'
            self.ticksDirection_resid['left'] = value
            self.ticksDirection_resid['right'] = value
          else:
            axis = 'x'
            self.ticksDirection_resid['top'] = value
            self.ticksDirection_resid['bottom'] = value

        # sets tick mark position
        axisobject.tick_params(axis=axis, direction=value, which='both')
        
        # remember settings
        self.rememberSetting[axisname + '_tickMarkDirection' + axis] = axisname + '.tick_params(axis=' + repr(axis) +', direction=' + repr(value) + ', which=\'both\')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()
          
  '''
  def setTickMarkDashStyle(self, value='in', axis='left', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['left', 'right', 'bottom', 'top']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget #; axisname = 'ax'; axisobject = self.ax
          if(self.ticksDashStyle[axis] == value):
            redraw = False
          # for time being, left/right and top/bottom are linked
          if (axis in ['left', 'right']):
            axis = 'y'
            self.ticksDashStyle['left'] = value
            self.ticksDashStyle['right'] = value
          else:
            axis = 'x'
            self.ticksDashStyle['top'] = value
            self.ticksDashStyle['bottom'] = value
        else:
          plotobject = self.residplotwidget #; axisname = 'ax_resid' ; axisobject = self.ax_resid
          if(self.ticksDashStyle_resid[axis] == value):
            redraw = False
          # for time being, left/right and top/bottom are linked
          if (axis in ['left', 'right']):
            axis = 'y'
            self.ticksDashStyle_resid['left'] = value
            self.ticksDashStyle_resid['right'] = value
          else:
            axis = 'x'
            self.ticksDashStyle_resid['top'] = value
            self.ticksDashStyle_resid['bottom'] = value

        # sets tick mark position
        # won't work as tick marks are bizarrely implented as markers (not lines)
        #axisobject.tick_params(axis=axis, capstyle=value, which='both')
        
        # remember settings
        #self.rememberSetting[axisname + '_tickMarkDashStyle' + axis] = axisname + '.tick_params(axis=' + repr(axis) +', capstyle=' + repr(value) + ', which=\'both\')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()
  '''

  def setTickMarkVisibility(self, value=True, axis='left', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['left', 'right', 'bottom', 'top']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.ticksVisible[axis] == value):
            redraw = False
          self.ticksVisible[axis] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.ticksVisible_resid[axis] == value):
            redraw = False
          self.ticksVisible_resid[axis] = value

        if(axis in ['left', 'right']):
          # modify ticks along y axes
          if(self.ticksVisible['left']):
            if(self.ticksVisible['right']):
              toshow = 'both'
            else:
              toshow = 'left'
            # first set labels to left side to return them there in case they have been removed previously
            axisobject.yaxis.set_ticks_position('left')
            axisobject.yaxis.set_ticks_position(toshow)
          else:
            if(self.ticksVisible['right']):
              toshow = 'right'
            else:
              toshow = 'none'
            axisobject.yaxis.set_ticks_position(toshow)
        else:
          # modify ticks along x axes
          if(self.ticksVisible['bottom']):
            if(self.ticksVisible['top']):
              toshow = 'both'
            else:
              toshow = 'bottom'
            # first set labels to bottom to return them there in case they have been removed previously
            axisobject.xaxis.set_ticks_position('bottom')
            axisobject.xaxis.set_ticks_position(toshow)
          else:
            if(self.ticksVisible['top']):
              toshow = 'top'
            else:
              toshow = 'none'
            axisobject.xaxis.set_ticks_position(toshow)
              
        # remember settings
        if(axis in ['left', 'right']):
          axis = 'y'
        else:
          axis = 'x'
        self.rememberSetting[axisname + '_tickMarkVisibility' + axis] = axisname + '.' + axis + 'axis.set_ticks_position(' + repr(toshow) + ')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setTickMarkColor(self, value=[0, 0, 0, 1], axis='left', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['left', 'right', 'bottom', 'top']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.ticksColor[axis] == value):
            redraw = False
          # for time being, left/right and top/bottom are linked
          if (axis in ['left', 'right']):
            axis = 'y'
            self.ticksColor['left'] = value
            self.ticksColor['right'] = value
          else:
            axis = 'x'
            self.ticksColor['top'] = value
            self.ticksColor['bottom'] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.ticksColor_resid[axis] == value):
            redraw = False
          # for time being, left/right and top/bottom are linked
          if (axis in ['left', 'right']):
            axis = 'y'
            self.ticksColor_resid['left'] = value
            self.ticksColor_resid['right'] = value
          else:
            axis = 'x'
            self.ticksColor_resid['top'] = value
            self.ticksColor_resid['bottom'] = value

        # sets axis label color
        axisobject.tick_params(axis=axis, color=value, which='both')
  
        # remember settings
        self.rememberSetting[axisname + '_tickMarkColor' + axis] = axisname + '.tick_params(axis=' + repr(axis) +', color=' + repr(value) + ', which=\'both\')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setTickMarkWidth(self, value=1.0, axis='left', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['left', 'right', 'bottom', 'top']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.ticksWidth[axis] == value):
            redraw = False
          # for time being, left/right and top/bottom are linked
          if (axis in ['left', 'right']):
            axis = 'y'
            self.ticksWidth['left'] = value
            self.ticksWidth['right'] = value
          else:
            axis = 'x'
            self.ticksWidth['top'] = value
            self.ticksWidth['bottom'] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.ticksWidth_resid[axis] == value):
            redraw = False
          self.ticksWidth_resid[axis] = value
          if (axis in ['left', 'right']):
            axis = 'y'
            self.ticksWidth_resid['left'] = value
            self.ticksWidth_resid['right'] = value
          else:
            axis = 'x'
            self.ticksWidth_resid['top'] = value
            self.ticksWidth_resid['bottom'] = value

        axisobject.tick_params(axis=axis, width=value, which='both')

        # remember settings
        self.rememberSetting[axisname + '_tickMarkWidth' + axis] = axisname + '.tick_params(axis=' + repr(axis) +', width=' + repr(value) + ', which=\'both\')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setTickMarkLength(self, value=1.0, axis='left', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['left', 'right', 'bottom', 'top']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.ticksLength[axis] == value):
            redraw = False
          # for time being, left/right and top/bottom are linked
          if (axis in ['left', 'right']):
            axis = 'y'
            self.ticksLength['left'] = value
            self.ticksLength['right'] = value
          else:
            axis = 'x'
            self.ticksLength['top'] = value
            self.ticksLength['bottom'] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.ticksLength_resid[axis] == value):
            redraw = False
          # for time being, left/right and top/bottom are linked
          if (axis in ['left', 'right']):
            axis = 'y'
            self.ticksLength_resid['left'] = value
            self.ticksLength_resid['right'] = value
          else:
            axis = 'x'
            self.ticksLength_resid['top'] = value
            self.ticksLength_resid['bottom'] = value

        axisobject.tick_params(axis=axis, length=value, which='major')
        axisobject.tick_params(axis=axis, length=value/2.0, which='minor')
        # remember settings
        self.rememberSetting[axisname + '_tickMarkLength' + axis] = axisname + '.tick_params(axis=' + repr(axis) +', length=' + repr(value) + ', which=\'major\')\n'
        self.rememberSetting[axisname + '_tickMarkLength' + axis] += axisname + '.tick_params(axis=' + repr(axis) +', length=' + repr(value/2.0) + ', which=\'minor\')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setAxisLabelColor(self, value=[0, 0, 0, 1], axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis == 'x'):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.labelXColor == value):
            redraw = False
          self.labelXColor = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.labelXColor_resid == value):
            redraw = False
          self.labelXColor_resid = value

        handleAxis = axisobject.xaxis.label
        handleAxis.set_color(value)
      else:
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.labelYColor == value):
            redraw = False
          self.labelYColor = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.labelYColor_resid == value):
            redraw = False
          self.labelYColor_resid = value

        handleAxis = axisobject.yaxis.label
        handleAxis.set_color(value)

      # remember settings
      self.rememberSetting[axisname + '_axisLabelColor' + axis] = axisname + '.' + axis + 'axis.label.set_color(' + repr(value) + ')\n'
      # redraw?
      if(redraw):
        plotobject.myRefresh()

  def setAxisLabel(self, labeltext=None, axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      # updates axis label
      if(labeltext == None):
        labeltext = axis

      if(axis == 'x'):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; figobject = self.matplot; axisname = 'ax'
          if(self.labelX == labeltext):
            redraw = False
          self.labelX = labeltext
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; figobject = self.residplot; axisname = 'ax_resid'
          if(self.labelX_resid == labeltext):
            redraw = False
          self.labelX_resid = labeltext
        # manually process escape characters
        labeltext = '\n'.join(labeltext.split('\\n'))
        labeltext = '\t'.join(labeltext.split('\\t'))
        # check for potential Mathtext errors
        prevLabel = axisobject.xaxis.get_label_text()
        axisobject.xaxis.set_label_text(labeltext)
        try:
          axisobject.xaxis.label._get_layout(figobject.canvas.renderer)
        except:
          # revert to previous label
          self.parent.statusbar.showMessage('Cannot set axis label to' + labeltext, self.parent.STATUS_TIME)
          
          axisobject.xaxis.set_label_text(prevLabel)
          labeltext = prevLabel
          redraw = False
      else:
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; figobject = self.matplot; axisname = 'ax'
          if(self.labelY == labeltext):
            redraw = False
          self.labelY = labeltext
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; figobject = self.residplot; axisname = 'ax_resid'
          if(self.labelY_resid == labeltext):
            redraw = False
          self.labelY_resid = labeltext
        # manually process escape characters
        labeltext = '\n'.join(labeltext.split('\\n'))
        labeltext = '\t'.join(labeltext.split('\\t'))
        if(target == 'resid'):
          labeltext = u'\N{GREEK CAPITAL LETTER DELTA}' + labeltext
        # check for potential Mathtext errors
        prevLabel = axisobject.yaxis.get_label_text()
        axisobject.yaxis.set_label_text(labeltext)
        try:
          axisobject.yaxis.label._get_layout(figobject.canvas.renderer)
        except:
          # revert to previous label
          self.parent.statusbar.showMessage('Cannot set axis label to' + labeltext, self.parent.STATUS_TIME)
          axisobject.yaxis.set_label_text(prevLabel)
          labeltext = prevLabel
          redraw = False
            
      # remember settings
      self.rememberSetting[axisname + '_axisLabel' + axis] = axisname + '.' + axis + 'axis.set_label_text(' + repr(labeltext) + ')\n'

      # capture errors with bad fonts (can occur when switching back from all-Mathtext label)
      try:
        if(redraw):
          plotobject.myRefresh()
      except:
        safeFont = 'DejaVu Sans'
        self.parent.statusbar.showMessage('Experiencing problems with font ' + self.axisFont[axis] + ' -- reverting to ' + safeFont, self.parent.STATUS_TIME)
        self.axisFont[axis] = safeFont
        if(axis == 'x'):
          axisobject.xaxis.label.set_fontname(safeFont)
        else:
          axisobject.yaxis.label.set_fontname(safeFont)

        # adjust remember settings 
        self.rememberSetting[axisname + '_axisFont' + axis] = axisname + '.' + axis + 'axis.label.set_fontname(' + repr(safeFont) + ')\n'

        if(redraw):
          plotobject.myRefresh()

  def setAxisVisibility(self, value=True, axis='left', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['left', 'right', 'bottom', 'top']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.axisVisible[axis] == value):
            redraw = False
          self.axisVisible[axis] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.axisVisible_resid[axis] == value):
            redraw = False
          self.axisVisible_resid[axis] = value

        # sets axis visibility
        axisobject.spines[axis].set_visible(value)

        # remember settings
        self.rememberSetting[axisname + '_axisVisibility' + axis] = axisname + '.spines[' + repr(axis) + '].set_visible(' + repr(value) + ')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setAxisColor(self, value=True, axis='left', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['left', 'right', 'bottom', 'top']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.axisColor[axis] == value):
            redraw = False
          self.axisColor[axis] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.axisColor_resid[axis] == value):
            redraw = False
          self.axisColor_resid[axis] = value

        axisobject.spines[axis].set_color(value)
        
        # remember settings
        self.rememberSetting[axisname + '_axisColor' + axis] = axisname + '.spines[' + repr(axis) + '].set_color(' + repr(value) + ')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setAxisWidth(self, value=1.0, axis='left', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['left', 'right', 'bottom', 'top']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.axisWidth[axis] == value):
            redraw = False
          self.axisWidth[axis] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.axisWidth_resid[axis] == value):
            redraw = False
          self.axisWidth_resid[axis] = value

        # updates axis width
        axisobject.spines[axis].set_linewidth(value)

        # remember settings
        self.rememberSetting[axisname + '_axisWidth' + axis] = axisname + '.spines[' + repr(axis) + '].set_linewidth(' + repr(value) + ')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setAxisFont(self, value=None, axis='x', redraw=True, target='plot'):
    defaultFont = 'DejaVu Sans'
    # check whether font exists
    if(not (value in self.parent.fontNames)):
      value = defaultFont
    if(value in self.parent.fontNames):
      # check whether to operate on data or resid plot
      if(target in ['plot', 'resid']):
        if(axis in ['x', 'y']):
          if(target == 'plot'):
            prevFont = self.axisFont[axis]
            plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
            if(self.axisFont[axis] == value):
              redraw = False
            self.axisFont[axis] = value
          else:
            prevFont = self.axisFont_resid[axis]
            plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
            if(self.axisFont_resid[axis] == value):
              redraw = False
            self.axisFont_resid[axis] = value

          if(axis == 'x'):
            axisobject.xaxis.label.set_fontname(value)
          else:
            axisobject.yaxis.label.set_fontname(value)

          # have to capture errors in case a strange font is set
          try:
            if(redraw):
              plotobject.myRefresh()
          except:
            self.parent.statusbar.showMessage('Experiencing problems setting font ' + value + ' -- reverting to ' + prevFont, self.parent.STATUS_TIME)
            
            # revert to previous font
            value = prevFont
            if(target == 'plot'):
              self.axisFont[axis] = prevFont
            else:
              self.axisFont_resid[axis] = prevFont

            if(axis == 'x'):
              axisobject.xaxis.label.set_fontname(prevFont)
            else:
              axisobject.yaxis.label.set_fontname(prevFont)

            # also capture errors with previous font (can happen if selecting two bad fonts in a row)
            try:
              if(redraw):
                plotobject.myRefresh()
            except:
              safeFont = 'DejaVu Sans'
              self.parent.statusbar.showMessage('Also experiencing problems setting font ' + self.legendLabelFont + ' -- reverting to ' + safeFont, self.parent.STATUS_TIME)

              # revert to previous font
              value = safeFont
              if(target == 'plot'):
                self.axisFont[axis] = safeFont
              else:
                self.axisFont_resid[axis] = safeFont
  
              if(axis == 'x'):
                axisobject.xaxis.label.set_fontname(safeFont)
              else:
                axisobject.yaxis.label.set_fontname(safeFont)

          # remember settings
          self.rememberSetting[axisname + '_axisFont' + axis] = axisname + '.' + axis + 'axis.label.set_fontname(' + repr(value) + ')\n'

  def setAxisLabelAlignment(self, value=None, axis='x', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['x', 'y']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'

        if(axis == 'x'):
          axisobject.xaxis.label.set_horizontalalignment(value)
          direction = 'horizontal'
          if(target == 'plot'):
            if(self.labelXAlignment == value):
              redraw = False
            self.labelXAlignment = value
          else:
            if(self.labelXAlignment_resid == value):
              redraw = False
            self.labelXAlignment_resid = value
        else:
          axisobject.yaxis.label.set_horizontalalignment(value)
          direction = 'horizontal'
          if(target == 'plot'):
            if(self.labelYAlignment == value):
              redraw = False
            self.labelYAlignment = value
          else:
            if(self.labelYAlignment_resid == value):
              redraw = False
            self.labelYAlignment_resid = value

        # remember settings
        self.rememberSetting[axisname + '_axisAlignment' + axis] = axisname + '.' + axis + 'axis.label.set_' + direction + 'alignment(' + repr(value) + ')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()
          
  def setTickFont(self, value=None, axis='x', redraw=True, target='plot'):
    defaultFont = 'DejaVu Sans'
    # check whether font exists
    if(not (value in self.parent.fontNames)):
      value = defaultFont
    if(value in self.parent.fontNames):
      # check whether to operate on data or resid plot
      if(target in ['plot', 'resid']):
        if(axis in ['x', 'y']):
          if(target == 'plot'):
            prevFont = self.tickFont[axis]
            plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
            if(self.tickFont[axis] == value):
              redraw = False
            self.tickFont[axis] = value
          else:
            prevFont = self.tickFont_resid[axis]
            plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
            if(self.tickFont_resid[axis] == value):
              redraw = False
            self.tickFont_resid[axis] = value
        
          # updates tick font
          if(axis == 'x'):
            tickLabels = axisobject.get_xticklabels(which='both')
            tickLabels.append(axisobject.xaxis.get_offset_text())
          else:
            tickLabels = axisobject.get_yticklabels(which='both')
            tickLabels.append(axisobject.yaxis.get_offset_text())
            
          for entry in tickLabels:
            entry.set_fontname(value)

          # have to capture errors in case a strange font is set
          try:
            if(redraw):
              plotobject.myRefresh()
          except:
            self.parent.statusbar.showMessage('Experiencing problems setting font ' + value + ' -- reverting to ' + prevFont, self.parent.STATUS_TIME)
            
            # revert to previous font
            value = prevFont
            if(target == 'plot'):
              self.tickFont[axis] = prevFont
            else:
              self.tickFont_resid[axis] = prevFont

            if(axis == 'x'):
              tickLabels = axisobject.get_xticklabels(which='both')
              tickLabels.append(axisobject.xaxis.get_offset_text())
            else:
              tickLabels = axisobject.get_yticklabels(which='both')
              tickLabels.append(axisobject.yaxis.get_offset_text())
              
            for entry in tickLabels:
              entry.set_fontname(prevFont)

            # also capture errors with previous font (can happen if selecting two bad fonts in a row)
            try:
              if(redraw):
                plotobject.myRefresh()
            except:
              safeFont = 'DejaVu Sans'
              self.parent.statusbar.showMessage('Also experiencing problems setting font ' + self.legendLabelFont + ' -- reverting to ' + safeFont, self.parent.STATUS_TIME)

              # revert to previous font
              value = safeFont
              if(target == 'plot'):
                self.tickFont[axis] = safeFont
              else:
                self.tickFont_resid[axis] = safeFont
  
              if(axis == 'x'):
                tickLabels = axisobject.get_xticklabels(which='both')
                tickLabels.append(axisobject.xaxis.get_offset_text())
              else:
                tickLabels = axisobject.get_yticklabels(which='both')
                tickLabels.append(axisobject.yaxis.get_offset_text())
                
              for entry in tickLabels:
                entry.set_fontname(safeFont)

          # remember settings
          self.rememberSetting[axisname + '_axisTickFont' + axis] = 'tickLabels = ' + axisname + '.get_' + axis + 'ticklabels()\n'
          self.rememberSetting[axisname + '_axisTickFont' + axis] += 'tickLabels.append(' + axisname + '.' + axis + 'axis.get_offset_text())\n'
          self.rememberSetting[axisname + '_axisTickFont' + axis] += 'for entry in tickLabels:\n\tentry.set_fontname(' + repr(value) + ')\n'

  def setAxisStyle(self, value='solid', axis='left', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['left', 'right', 'bottom', 'top']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.axisStyle[axis] == value):
            redraw = False
          self.axisStyle[axis] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.axisStyle_resid[axis] == value):
            redraw = False
          self.axisStyle_resid[axis] = value

        axisobject.spines[axis].set_linestyle(self.axisStyle[axis])

        # remember settings
        self.rememberSetting[axisname + '_axisStyle' + axis] = axisname + '.spines[' + repr(axis) + '].set_linestyle(' + repr(value) + ')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setAxisDashStyle(self, value='solid', axis='left', redraw=True, target='plot'):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      if(axis in ['left', 'right', 'bottom', 'top']):
        if(target == 'plot'):
          plotobject = self.dataplotwidget; axisobject = self.ax; axisname = 'ax'
          if(self.axisDashStyle[axis] == value):
            redraw = False
          self.axisDashStyle[axis] = value
        else:
          plotobject = self.residplotwidget; axisobject = self.ax_resid; axisname = 'ax_resid'
          if(self.axisDashStyle_resid[axis] == value):
            redraw = False
          self.axisDashStyle_resid[axis] = value

        axisobject.spines[axis].set_capstyle(self.axisDashStyle[axis])

        # remember settings
        self.rememberSetting[axisname + '_axisDashStyle' + axis] = axisname + '.spines[' + repr(axis) + '].set_capstyle(' + repr(value) + ')\n'
        # redraw?
        if(redraw):
          plotobject.myRefresh()

  def setAutoScale(self, axis='x'):
    # updates autoscale options for axes
    if(axis in ['x', 'y']):
      if(axis == 'x'):
        state = self.autoScaleCheckX.isChecked()
        self.autoScaleX = state
      else:
        state = self.autoScaleCheckY.isChecked()
        self.autoScaleY = state
        
      # rescale contents on setting auto to True
      if(state):
        currData, currRoles = self.parent.data[self.parent.activeData].getData_n_Fit()
        if(('x' in currRoles) and (len(list(currData[:, currRoles.index('x')])))):
          # we have some data that we could zoom to
          if(axis == 'x'):
            xval = list(currData[:, currRoles.index('x')])
            if('xerr' in currRoles):
              xerr = list(currData[:, currRoles.index('xerr')])
              temp_xmin = np.min([i-j for i, j in zip(xval, xerr)])
              temp_xmax = np.max([i+j for i, j in zip(xval, xerr)])
            else:
              temp_xmin = np.min(xval)
              temp_xmax = np.max(xval)
              
            # ensure minimum limit
            if(temp_xmax - temp_xmin < self.EPSILON):
              temp_xmax += self.EPSILON; temp_xmin -= self.EPSILON
            elif(self.data_spacer > 0):
              if(self.modeX == 'linear'):
                difference = temp_xmax - temp_xmin
                temp_xmax += difference * self.data_spacer
                temp_xmin -= difference * self.data_spacer
              else:
                # log scale -- isolate positive data
                pos_x = np.array(xval)
                pos_x = pos_x[pos_x > 0]
                # recalc. xmin to address error when restoring state
                temp_xmin = np.min(pos_x)
                if(len(pos_x > 1)):
                  difference = np.log(pos_x[-1] / pos_x[0])
                  temp_xmin = np.exp(np.log(temp_xmin) - self.data_spacer * difference)
                  temp_xmax = np.exp(np.log(temp_xmax) + self.data_spacer * difference)
                  
            self.setAxisLimits(lower=temp_xmin, upper=temp_xmax, axis='x', updateLabel=True, redraw=True)
          else:
            yval = list(currData[:, currRoles.index('y')])
            if(len(yval)):
              #print(yval)
              if('yerr' in currRoles):
                yerr = list(currData[:, currRoles.index('yerr')])
                temp_ymin = np.min([i-j for i, j in zip(yval, yerr)])
                temp_ymax = np.max([i+j for i, j in zip(yval, yerr)])
              else:
                temp_ymin = np.min(yval)
                temp_ymax = np.max(yval)

              # ensure minimum limit
              if (temp_ymax-temp_ymin<self.EPSILON):
                temp_ymax += self.EPSILON; temp_ymin -= self.EPSILON
              elif(self.data_spacer > 0):
                if(self.modeY == 'linear'):
                  difference = temp_ymax - temp_ymin
                  temp_ymax += difference * self.data_spacer
                  temp_ymin -= difference * self.data_spacer
                else:
                  # log scale -- isolate positive data
                  pos_y = np.array(yval)
                  pos_y = pos_y[pos_y > 0]
                  if(len(pos_y > 1)):
                    difference = np.log(pos_y[-1] / pos_y[0])
                    temp_ymin = np.exp(np.log(temp_ymin) - self.data_spacer * difference)
                    temp_ymax = np.exp(np.log(temp_ymax) + self.data_spacer * difference)
      
              self.setAxisLimits(lower = temp_ymin, upper = temp_ymax, axis = 'y', updateLabel = True, redraw=True)

  def rectSelectorCallback(self, event_click, event_release):
    # handles interactive zoom in plot
    MIN_SELECTION_BOX = 5
    flag = False
    # handle button reactions
    if(event_click.button == 1):
      # check wether selection box is at least minimum size
      if((np.abs(event_click.x - event_release.x) >= MIN_SELECTION_BOX) and (np.abs(event_click.y - event_release.y) >= MIN_SELECTION_BOX)):
        # left mouse button => zoom
        # only proceed if at least one coord changed since last click (this is to prevent rectangle selector from misbehainvg)
        if((event_click.x != self.previousClick[0]) or (event_click.y != self.previousClick[1]) or (event_release.x != self.previousClick[2]) or (event_release.y != self.previousClick[3])):
          x1, y1 = event_click.xdata, event_click.ydata
          x2, y2 = event_release.xdata, event_release.ydata
          xmin = np.min((x1, x2)); xmax = np.max((x1, x2))
          ymin = np.min((y1, y2)); ymax = np.max((y1, y2))
          
          # store current axis limits
          self.storeCoord.extend((self.minX, self.minY, self.maxX, self.maxY))
          flag = True
          
          # update self.previousClick
          self.previousClick = [event_click.x, event_click.y, event_release.x, event_release.y]
    elif(event_click.button == 3):
      # update self.previousClick
      self.previousClick = [event_click.x, event_click.y, event_release.x, event_release.y]
      # right mouse button => unzoom
      if(len(self.storeCoord) > 0):
        #print(3333)
        [xmin, ymin, xmax, ymax] = self.storeCoord[-4:]
        self.storeCoord = self.storeCoord[:-4]
        flag = True
        
    # set axes limits if required
    if(flag):
      self.setAxisLimits(lower = xmin, upper = xmax, axis = 'x', updateLabel = True, target='plot', redraw=False)
      self.setAxisLimits(lower = xmin, upper = xmax, axis = 'x', updateLabel = False, target='resid', redraw=False)
      # trigger redrawing of fit function with new axis limits
      if(self.modeX == 'linear'):
        plot_interval = np.linspace(self.minX, self.maxX, self.DATAPOINTS_SIMULATION)
      elif(self.modeX == 'log'):
        plot_interval = np.linspace(np.log(self.minX), np.log(self.maxX), self.DATAPOINTS_SIMULATION)
        plot_interval = np.exp(plot_interval)
        
      self.parent.fit[self.parent.activeFit].handlePlot = self.plotFunction(\
        fitobject = self.parent.fit[self.parent.activeFit], x = plot_interval,\
        handlePlot = self.parent.fit[self.parent.activeFit].handlePlot, redraw=False)
      self.handleResidZero = self.plotResidZero(self.handleResidZero, redraw=True)
 
      # reset y axis
      self.setAxisLimits(lower=ymin, upper=ymax, axis='y', updateLabel=True, target='plot', redraw=True)
      # overcome the blitting
      self.rectSelector.to_draw.set_visible(False)
      # issue extra draw on OS X to let RectSel disappear for good
      if(sys.platform == 'darwin'):
        self.matplot.canvas.draw()
        self.matplot.canvas.flush_events()
      else:
        self.matplot.canvas.flush_events()

  def setPathStroke(self, state=True, redraw=True):
    # applies path stroke
    self.applyPathStroke = state
    self.setPathEffects(redraw=redraw)

  def setPathStrokeColor(self, value=4*[0.0], redraw=True):
    # changes color of path stroke
    self.pathStrokeColor = value
    # do the path setting draw?
    if((redraw) and (self.applyPathStroke)):
      self.setPathEffects(redraw=redraw)

  def setPathStrokeWidth(self, value=1.0, redraw=True):
    # changes witdth of path stroke
    self.pathStrokeWidth = value
    # do the path setting draw?
    if((redraw) and (self.applyPathStroke)):
      self.setPathEffects(redraw=redraw)

  def setPathShadow(self, state=True, redraw=True):
    # applies path shadow
    self.applyPathShadow = state
    self.setPathEffects(redraw=redraw)

  def setPathShadowColor(self, value=4*[0.0], redraw=True):
    # changes color of path shadow
    self.pathShadowColor = value
    self.pathShadowAlpha = value[-1]
    # do the path setting draw?
    if((redraw) and (self.applyPathShadow)):
      self.setPathEffects(redraw=redraw)

  def setPathShadowOffset(self, value=1.0, direction='x', redraw=True):
    # changes offset of path shadow
    if(direction in ['x', 'y']):
      if(direction == 'x'):
        self.pathShadowX = value
      else:
        self.pathShadowY = value
      # do the path setting draw?
      if((redraw) and (self.applyPathShadow)):
        self.setPathEffects(redraw=redraw)

  def setPathEffects(self, redraw=True):
    # applies path effects
    if(self.applyPathStroke):
      baseEffect = []
      tempRememberSetting = ''
    else:
      baseEffect = [PathEffects.Normal()]
      tempRememberSetting = 'PathEffects.Normal()'

    if(self.applyPathShadow):
      pathShadowX = self.pathShadowX
      pathShadowY = self.pathShadowY
      pathShadowColor = self.pathShadowColor
      pathShadowAlpha = self.pathShadowAlpha
      baseEffect = [PathEffects.SimpleLineShadow(offset=(pathShadowX, pathShadowY), shadow_color=pathShadowColor,\
        alpha=pathShadowAlpha)] + baseEffect
      tempRememberSetting2 = 'PathEffects.SimpleLineShadow(offset=(' + repr(pathShadowX) + ',' + repr(pathShadowY) + '), shadow_color=' +\
        repr(pathShadowColor) + ', alpha=' + repr(pathShadowAlpha) +')'

      if(len(tempRememberSetting)):
        tempRememberSetting += ',\n\t' + tempRememberSetting2
      else:
        tempRememberSetting = tempRememberSetting2
    
    # deal with existing objects
    if(self.applyPathStroke):
      pathStrokeWidth = self.pathStrokeWidth
      pathStrokeColor = self.pathStrokeColor

      # modify existing extras
      for entry in self.parent.extras:
        if(entry.handle != None):
          if(hasattr(entry.handle, 'get_lw')):
            curr_linewidth = 2 * pathStrokeWidth + entry.handle.get_lw()
          else:
            curr_linewidth = 2 * pathStrokeWidth + 1
          entry.handle.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
          # set bbox if present
          if(hasattr(entry.handle, 'get_bbox_patch')):
            handle = entry.handle.get_bbox_patch()
            if(handle != None):
              curr_linewidth = 2 * pathStrokeWidth + handle.get_lw()
              handle.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
          # set arrow patch if present
          if(hasattr(entry.handle, 'arrow_patch')):
            handle = entry.handle.arrow_patch
            if(handle != None):
              curr_linewidth = 2 * pathStrokeWidth + handle.get_lw()
              handle.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])

      # modify existing curves
      for entry in self.parent.fit:
        if(entry.handlePlot != None):
          curr_linewidth = 2 * pathStrokeWidth + entry.handlePlot.get_lw()
          entry.handlePlot.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
  
      # modify existing data sets
      for entry in self.parent.data:
        if(entry.handleData != None):
          curr_linewidth = 2 * pathStrokeWidth + entry.handleData.get_lw()
          entry.handleData.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
        if(entry.handleResid != None):
          curr_linewidth = 2 * pathStrokeWidth + entry.handleResid.get_lw()
          entry.handleResid.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
        if(entry.handleBar != None):
          children = entry.handleBar.get_children()
          for entry2 in children:
            curr_linewidth = 2 * pathStrokeWidth + entry2.get_lw()
            entry2.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
        # don't apply to stack style, throws strange error
        #if(entry.handleStack != None):
          #entry.handleStack.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
        if(entry.handleErr != None):
          curr_linewidth = 2 * pathStrokeWidth + entry.handleErr[0].get_lw()
          entry.handleErr[0].set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
          print(entry.handleErr[1])
          for entry2 in entry.handleErr[1]:
            # remember caps are drawn as markers not lines
            if(entry2.get_markeredgewidth() > 0):
              curr_linewidth = 2 * pathStrokeWidth + entry2.get_markeredgewidth()
              entry2.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
            else:
              # don't draw effects for zero width markers
              #entry2.set_path_effects(baseEffect)
              # in this case don't do anything since setting path effects would cause drawing of caps (w/ currently set path effects)
              pass
          for entry2 in entry.handleErr[2]:
            # have to use get_linewidth() here as get_lw() not implemented?!
            curr_linewidth = 2 * pathStrokeWidth + entry2.get_linewidth()
            entry2.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
       
      # modify axes
      for entry in self.ax.spines:
        curr_linewidth = 2 * pathStrokeWidth + self.ax.spines[entry].get_lw()
        self.ax.spines[entry].set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
      for entry in self.ax_resid.spines:
        curr_linewidth = 2 * pathStrokeWidth + self.ax_resid.spines[entry].get_lw()
        self.ax_resid.spines[entry].set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])

      # modify grid lines
      for entry in self.ax.xaxis.get_gridlines():
        curr_linewidth = 2 * pathStrokeWidth + entry.get_lw()
        entry.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
      for entry in self.ax.yaxis.get_gridlines():
        curr_linewidth = 2 * pathStrokeWidth + entry.get_lw()
        entry.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
      for entry in self.ax_resid.xaxis.get_gridlines():
        curr_linewidth = 2 * pathStrokeWidth + entry.get_lw()
        entry.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
      for entry in self.ax_resid.yaxis.get_gridlines():
        curr_linewidth = 2 * pathStrokeWidth + entry.get_lw()
        entry.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
        
      # modify tick lines
      for entry in self.ax.xaxis.get_ticklines():
        curr_linewidth = 2 * pathStrokeWidth + entry.get_lw()
        entry.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
      for entry in self.ax.yaxis.get_ticklines():
        curr_linewidth = 2 * pathStrokeWidth + entry.get_lw()
        entry.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
      for entry in self.ax_resid.xaxis.get_ticklines():
        curr_linewidth = 2 * pathStrokeWidth + entry.get_lw()
        entry.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
      for entry in self.ax_resid.yaxis.get_ticklines():
        curr_linewidth = 2 * pathStrokeWidth + entry.get_lw()
        entry.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
  
      # zero line
      if(self.handleResidZero != None):
        curr_linewidth = 2 * pathStrokeWidth + self.handleResidZero.get_lw()
        self.handleResidZero.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])

      # and the cursor
      if(self.cursor != None):
        handles = self.cursor.getHandles()
        for entry in handles:
          if(hasattr(entry, 'get_lw')):
            curr_linewidth = 2 * pathStrokeWidth + entry.get_lw()
          else:
            curr_linewidth = 2 * pathStrokeWidth + 1
          entry.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])

      # and the axes labels
      curr_linewidth = 2 * pathStrokeWidth + 1
      for entry in [self.ax, self.ax_resid]:
        entry.xaxis.label.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])
        entry.yaxis.label.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])

      # and the tick labels
      curr_linewidth = 2 * pathStrokeWidth + 1
      tickLabels = []
      for entry in [self.ax, self.ax_resid]:
        tickLabels.extend(entry.get_xticklabels(which='both'))
        tickLabels.extend(entry.get_yticklabels(which='both'))
        tickLabels.append(entry.xaxis.get_offset_text())
        tickLabels.append(entry.yaxis.get_offset_text())
      for entry in tickLabels:
        entry.set_path_effects(baseEffect + [PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor)])

      # update baseEffect for new plot items
      curr_linewidth = 2 * pathStrokeWidth + 1.0
      baseEffect.append(PathEffects.withStroke(linewidth=curr_linewidth, foreground=pathStrokeColor))
      tempRememberSetting2 = 'PathEffects.withStroke(linewidth=' + repr(curr_linewidth) + ', foreground=' + repr(pathStrokeColor) +')'
      if(len(tempRememberSetting)):
        tempRememberSetting += ',\n\t' + tempRememberSetting2
      else:
        tempRememberSetting = tempRememberSetting2
    else:
      # modify existing extras
      for entry in self.parent.extras:
        if(entry.handle != None):
          entry.handle.set_path_effects(baseEffect)
          # set bbox if present
          if(hasattr(entry.handle, 'get_bbox_patch')):
            handle = entry.handle.get_bbox_patch()
            if(handle != None):
              handle.set_path_effects(baseEffect)
          # set arrow patch if present
          if(hasattr(entry.handle, 'arrow_patch')):
            handle = entry.handle.arrow_patch
            if(handle != None):
              handle.set_path_effects(baseEffect)

      # modify existing curves
      for entry in self.parent.fit:
        if(entry.handlePlot != None):
          entry.handlePlot.set_path_effects(baseEffect)
  
      # modify existing data sets
      for entry in self.parent.data:
        if(entry.handleData != None):
          entry.handleData.set_path_effects(baseEffect)
        if(entry.handleResid != None):
          entry.handleResid.set_path_effects(baseEffect)
        if(entry.handleBar != None):
          children = entry.handleBar.get_children()
          for entry2 in children:
            entry2.set_path_effects(baseEffect)
        # don't apply to stack style, throws strange error
        if(entry.handleErr != None):
          entry.handleErr[0].set_path_effects(baseEffect)
          for entry2 in entry.handleErr[1]:
            entry2.set_path_effects(baseEffect)
          for entry2 in entry.handleErr[2]:
            entry2.set_path_effects(baseEffect)
       
      # modify axes
      for entry in self.ax.spines:
        self.ax.spines[entry].set_path_effects(baseEffect)
      for entry in self.ax_resid.spines:
        self.ax_resid.spines[entry].set_path_effects(baseEffect)

      # modify grid lines
      for entry in self.ax.xaxis.get_gridlines():
        entry.set_path_effects(baseEffect)
      for entry in self.ax.yaxis.get_gridlines():
        entry.set_path_effects(baseEffect)
      for entry in self.ax_resid.xaxis.get_gridlines():
        entry.set_path_effects(baseEffect)
      for entry in self.ax_resid.yaxis.get_gridlines():
        entry.set_path_effects(baseEffect)

      # modify tick lines
      for entry in self.ax.xaxis.get_ticklines():
        entry.set_path_effects(baseEffect)
      for entry in self.ax.yaxis.get_ticklines():
        entry.set_path_effects(baseEffect)
      for entry in self.ax_resid.xaxis.get_ticklines():
        entry.set_path_effects(baseEffect)
      for entry in self.ax_resid.yaxis.get_ticklines():
        entry.set_path_effects(baseEffect)

      # zero line
      if(self.handleResidZero != None):
        self.handleResidZero.set_path_effects(baseEffect)

      # and the axes labels
      for entry in [self.ax, self.ax_resid]:
        entry.xaxis.label.set_path_effects(baseEffect)
        entry.yaxis.label.set_path_effects(baseEffect)

      # and the tick labels
      tickLabels = []
      for entry in [self.ax, self.ax_resid]:
        tickLabels.extend(entry.get_xticklabels(which='both'))
        tickLabels.extend(entry.get_yticklabels(which='both'))
        tickLabels.append(entry.xaxis.get_offset_text())
        tickLabels.append(entry.yaxis.get_offset_text())
      for entry in tickLabels:
        entry.set_path_effects(baseEffect)

      # and the cursor
      if(self.cursor != None):
        handles = self.cursor.getHandles()
        for entry in handles:
          entry.set_path_effects(baseEffect)

    # introduces path effects for new plot items
    tempDict = {}
    tempDict['path.effects'] = baseEffect
    matplotlib.rcParams.update(tempDict)

    self.rememberSetting['pathEffects'] = 'tempDict = {\'path.effects\': [' + tempRememberSetting + ']}\n'
    self.rememberSetting['pathEffects'] += 'matplotlib.rcParams.update(tempDict)\n'

    # update plot
    if(redraw):
      self.dataplotwidget.myRefresh()
      self.residplotwidget.myRefresh()
    
  def setXkcdSetting(self, value=1.0, item='scale', redraw=True):
    # update xckd setttings
    if(item in ['scale', 'length', 'random']):
      if(item == 'scale'):
        if(self.xkcdScale == value):
          redraw = False
        else:
          self.xkcdScale = value
      elif(item == 'length'):
        if(self.xkcdLength == value):
          redraw = False
        else:
          self.xkcdLength = value
      elif(item == 'random'):
        if(self.xkcdRandomness == value):
          redraw = False
        else:
          self.xkcdRandomness = value
          
      # do the xkcdify?
      if((redraw) and (self.xkcd)):
        self.xkcdify(state=self.xkcd, redraw=redraw)

  def xkcdify(self, state=True, redraw=True):
    # set xkcd-like parameters
    # store previous parameters
    if((not self.xkcd) and (state)):
      if ('font.sans-serif' in matplotlib.rcParams):
        self.xkcdStoreFonts = matplotlib.rcParams['font.sans-serif']
      else:
        self.xkcdStoreFonts = ['DejaVu Sans']
    
    # set new parameters
    self.xkcd = state
    tempDict = {}
    if(self.xkcd):
      xkcdScale = self.xkcdScale
      xkcdLength = self.xkcdLength
      xkcdRandomness = self.xkcdRandomness

      # check for presence of funny fonts
      addFonts = []
      fontCandidates = 'Humor Sans,Comic Sans MS'.split(',')
      for entry in fontCandidates:
        if entry in self.parent.fontNames:
          addFonts.append(entry)
          
      if(len(addFonts)):
        tempDict['font.sans-serif'] = addFonts
        tempDict['font.sans-serif'].extend(self.xkcdStoreFonts)
    else:
      xkcdScale = 0
      xkcdLength = 0
      xkcdRandomness = 0
      
      # restore original fonts
      tempDict['font.sans-serif'] = self.xkcdStoreFonts

    # introduces xkcd-type style for new plot items
    tempDict['path.sketch'] = (xkcdScale, xkcdLength, xkcdRandomness)
    matplotlib.rcParams.update(tempDict)
    self.rememberSetting['xkcd'] = 'tempDict = ' + repr(tempDict) + '\n'
    self.rememberSetting['xkcd'] += 'matplotlib.rcParams.update(tempDict)\n'
    
    # modify existing extras
    for entry in self.parent.extras:
      if(entry.handle != None):
        # modify object directly (for line)
        if(hasattr(entry.handle, 'set_sketch_params')):
          entry.handle.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
        # set bbox if present
        if(hasattr(entry.handle, 'get_bbox_patch')):
          handle = entry.handle.get_bbox_patch()
          if(handle != None):
            handle.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
        # set arrow patch if present
        if(hasattr(entry.handle, 'arrow_patch')):
          handle = entry.handle.arrow_patch
          if(handle != None):
            handle.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
    
    # modify existing curves
    for entry in self.parent.fit:
      if(entry.handlePlot != None):
        entry.handlePlot.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
    
    # modify existing data sets
    for entry in self.parent.data:
      if(entry.handleData != None):
        entry.handleData.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
      if(entry.handleResid != None):
        entry.handleResid.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
      if(entry.handleBar != None):
        children = entry.handleBar.get_children()
        for entry2 in children:
          entry2.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
      if(entry.handleStack != None):
        entry.handleStack.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
      if(entry.handleErr != None):
        entry.handleErr[0].set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
        for entry2 in entry.handleErr[1]:
          entry2.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
        for entry2 in entry.handleErr[2]:
          entry2.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
     
    # modify axes and background
    for entry in self.ax.spines:
      self.ax.spines[entry].set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
    for entry in self.ax_resid.spines:
      self.ax_resid.spines[entry].set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
    self.ax.patch.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
    self.ax_resid.patch.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
    
    # modify grid lines
    for entry in self.ax.xaxis.get_gridlines():
      entry.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
    for entry in self.ax.yaxis.get_gridlines():
      entry.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
    for entry in self.ax_resid.xaxis.get_gridlines():
      entry.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
    for entry in self.ax_resid.yaxis.get_gridlines():
      entry.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
      
    # modify tick lines (somehow not heeded by matplotlib?!)
    for entry in self.ax.xaxis.get_ticklines():
      entry.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
    for entry in self.ax.yaxis.get_ticklines():
      entry.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
    for entry in self.ax_resid.xaxis.get_ticklines():
      entry.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
    for entry in self.ax_resid.yaxis.get_ticklines():
      entry.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)

    # zero line
    if(self.handleResidZero != None):
      self.handleResidZero.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
      
    # and the cursor
    if(self.cursor != None):
      handles = self.cursor.getHandles()
      for entry in handles:
        entry.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)

    # and the axes labels
    for entry in [self.ax, self.ax_resid]:
      entry.xaxis.label.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)
      entry.yaxis.label.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)

    # and the tick labels
    tickLabels = []
    for entry in [self.ax, self.ax_resid]:
      tickLabels.extend(entry.get_xticklabels(which='both'))
      tickLabels.extend(entry.get_yticklabels(which='both'))
    for entry in tickLabels:
      entry.set_sketch_params(xkcdScale, xkcdLength, xkcdRandomness)

    # update plot
    if(redraw):
      self.dataplotwidget.myRefresh()
      self.residplotwidget.myRefresh()
    
  def initPlot(self, initialize=True):
    if(initialize):
      plt.ioff()
      # initialize data plot
      self.ax = self.matplot.add_subplot(111)
      self.ax.autoscale(enable = False, axis = 'both')
      self.matplot.patch.set_facecolor(self.canvasColor)
      self.dataplotwidget.myRefresh()
      
      # initalize some values
      self.handleData = None
      self.handlePlot = None
      self.handleErr = None
    
      # initialize resid plot
      self.ax_resid = self.residplot.add_subplot(111)
      self.ax_resid.autoscale(enable=False, axis='both')
      self.residplot.patch.set_facecolor(self.canvasColor)
      self.residplotwidget.myRefresh()
      
      # initalize some values
      self.handleResid = None
      self.handleResidZero = None
      self.handlesAbout = []
      
      # intiialize the plot rectangle selector
      rectprops = dict(fill=True, linewidth=1, facecolor=[0,0,1,0.4], edgecolor='black', linestyle='solid')
      if(('linux' in sys.platform) or (sys.platform == 'darwin')):
        self.rectSelector = RectSel(self.ax, self.rectSelectorCallback, drawtype='box', useblit=True, rectprops=rectprops,\
                                  button=[1,3], minspanx=0, minspany=0, spancoords='pixels')#, interactive=False)
      else:
        self.rectSelector = RectSel(self.ax, self.rectSelectorCallback, drawtype='box', useblit=True, rectprops=rectprops,\
                                  button=[1,3], minspanx=0, minspany=0, spancoords='pixels', interactive=False)
      # fudge to prevent rectangle selector from firing same event twice
      self.previousClick = [0.0] * 4
      
      # set up cursor
      self.matplot.canvas.mpl_connect('button_press_event', self.toggleCrossHair)
      
    for target in ['plot', 'resid']:
      # labels etc.
      self.setAxisLabel(self.labelX, axis='x', redraw=False, target=target)
      self.setAxisLabelColor(value = self.labelXColor, axis = 'x', redraw = False, target=target)
      self.setAxisLabelSize(value = self.labelXSize, axis = 'x', redraw = False, target=target)
      self.setAxisLabelAlignment(value = self.labelXAlignment, axis = 'x', redraw = False, target=target)
      self.setAxisLabelPad(value = self.labelXPad, axis = 'x', redraw = False, target=target)
      self.setAxisLabelPos(value = self.labelXPos, axis = 'x', redraw = False, target=target)
      self.setAxisLabelAngle(value = self.labelXAngle, axis = 'x', redraw = False, target=target)
      self.setAxisFont(value = self.axisFont['x'], axis = 'x', redraw = False, target=target)
      if(target == 'plot'):
        self.setAxisLabel(labeltext=self.labelY, axis='y', redraw=False, target=target)
      else:
        self.setAxisLabel(labeltext=self.labelY, axis='y', redraw=False, target=target)
      self.setAxisLabelColor(value = self.labelYColor, axis = 'y', redraw = False, target=target)
      self.setAxisLabelSize(value = self.labelYSize, axis = 'y', redraw = False, target=target)
      self.setAxisLabelAlignment(value = self.labelYAlignment, axis = 'y', redraw = False, target=target)
      self.setAxisLabelPad(value = self.labelYPad, axis = 'y', redraw = False, target=target)
      self.setAxisLabelPos(value = self.labelYPos, axis = 'y', redraw = False, target=target)
      self.setAxisLabelAngle(value = self.labelYAngle, axis = 'y', redraw = False, target=target)
      self.setAxisFont(value = self.axisFont['y'], axis = 'y', redraw = False, target=target)
      
      # set axes properties
      for key in self.axisVisible:
        self.setAxisVisibility(value = self.axisVisible[key], axis = key, redraw = False, target=target)
      for key in self.axisWidth:
        self.setAxisWidth(value = self.axisWidth[key], axis = key, redraw = False, target=target)
      for key in self.axisStyle:
        self.setAxisStyle(value = self.axisStyle[key], axis = key, redraw = False, target=target)
      for key in self.axisDashStyle:
        self.setAxisDashStyle(value = self.axisDashStyle[key], axis = key, redraw = False, target=target)
      for key in self.axisColor:
        self.setAxisColor(value = self.axisColor[key], axis = key, redraw = False, target=target)
        
      # set axes arrows
      for axis in ['x', 'y']:
        self.setAxisArrowColor(value=self.arrowColor[axis], axis=axis, item='line', redraw=False)
        self.setAxisArrowColor(value=self.arrowFill[axis], axis=axis, item='fill', redraw=False)
        self.setAxisArrowHeadWidth(value=self.arrowHeadWidth[axis], axis=axis, redraw=False)
        self.setAxisArrowHeadLength(value=self.arrowHeadLength[axis], axis=axis, redraw=False)
        self.setAxisArrowOverhang(value=self.arrowOverhang[axis], axis=axis, redraw=False)
        self.setAxisArrow(state=self.arrowVisible[axis], axis=axis, redraw=False, target=target)
  
      # set color and size of ticks
      self.setTickLabelColor(value = self.ticksXColor, axis = 'x', redraw = False, target=target)
      self.setTickLabelSize(value = self.ticksXSize, axis = 'x', redraw = False, target=target)
      self.setTickLabelAngle(value = self.ticksXAngle, axis = 'x', redraw = False, target=target)
      self.setTickFont(value = self.tickFont['x'], axis = 'x', redraw = False, target=target)
      self.setTickLabelColor(value = self.ticksYColor, axis = 'y', redraw = False, target=target)
      self.setTickLabelSize(value = self.ticksYSize, axis = 'y', redraw = False, target=target)
      self.setTickLabelAngle(value = self.ticksYAngle, axis = 'y', redraw = False, target=target)
      self.setTickFont(value = self.tickFont['y'], axis = 'y', redraw = False, target=target)
  
      # set tick properties
      for key in self.ticksVisible:
        self.setTickMarkVisibility(value = self.ticksVisible[key], axis = key, redraw = False, target=target)
      for key in self.ticksWidth:
        self.setTickMarkWidth(value = self.ticksWidth[key], axis = key, redraw = False, target=target)
      for key in self.ticksLength:
        self.setTickMarkLength(value = self.ticksLength[key], axis = key, redraw = False, target=target)
      for key in self.ticksColor:
        self.setTickMarkColor(value = self.ticksColor[key], axis = key, redraw = False, target=target)
      for key in self.ticksDirection:
        self.setTickMarkDirection(value = self.ticksDirection[key], axis = key, redraw = False, target=target)
  
      # set grid properties
      for key in self.gridVisible:
        self.setGridVisibility(value = self.gridVisible[key], axis = key, redraw = False, target=target)
      for key in self.gridWidth:
        self.setGridWidth(value = self.gridWidth[key], axis = key, redraw = False, target=target)
      for key in self.gridStyle:
        self.setGridStyle(value = self.gridStyle[key], axis = key, redraw = False, target=target)
      for key in self.gridDashStyle:
        self.setGridDashStyle(value = self.gridDashStyle[key], axis = key, redraw = False, target=target)
      for key in self.gridColor:
        self.setGridColor(value = self.gridColor[key], axis = key, redraw = False, target=target)
      for key in self.gridOrder:
        self.setGridOrder(value = self.gridOrder[key], axis = key, redraw = False, target=target)

      # canvas color etc.
      self.setCanvasColor(value=self.canvasColor, redraw=False, target=target)
      self.setFigureColor(value=self.figureColor, redraw=False, target=target)
      
      # set padding
      self.setPadding(value=self.padSize['bottom'], axis='bottom', redraw=False, target=target)

    # xkcd etc.
    self.xkcdify(state=self.xkcd, redraw=False)
    self.setPathEffects(redraw=False)
    
    # deal with axis ticks
    if(self.ticksXAuto):
      self.setAutoTicks(axis='x', redraw=False, target='plot')
      self.setAutoTicks(axis='x', redraw=False, target='resid')
    else:
      ticksXLabel = self.ticksXLabel
      self.setAxisTicks(value=self.ticksX, axis='x', redraw=False, target='plot')
      self.setAxisTicks(value=self.ticksX, axis='x', redraw=False, target='resid')
      # apply axis labels?
      self.ticksXLabel = ticksXLabel
      if(len(self.ticksXLabel)):
        for axisobject in [self.ax, self.ax_resid]:
          axisobject.xaxis.set_ticklabels(self.ticksXLabel)
          #nullLabels = matplotlib.ticker.NullFormatter()
          #axisobject.xaxis.set_minor_formatter(nullLabels)
      
    if(self.ticksYAuto):
      self.setAutoTicks(axis='y', redraw=False, target='plot')
    else:
      self.setAxisTicks(value=self.ticksY, axis='y', redraw=False, target='plot')
      
    if(self.ticksResidYAuto):
      self.setAutoTicks(axis='resid', redraw=False, target='resid')
    else:
      self.setAxisTicks(value=self.ticksResidY, axis='resid', redraw=False, target='resid')

    # retrieve axis ticks
    self.ticksX = self.getAxisTicks(axis = 'x')
    self.ticksY = self.getAxisTicks(axis = 'y')
    self.ticksResidY = self.getAxisTicks(axis = 'resid')
    #print(self.ticksX, self.ticksY, self.ticksResidY)

    # issue plot redraw
    # the follwing call not needed as we will draw a curve afterwards
    self.handleResidZero = self.plotResidZero(self.handleResidZero, redraw=False)
    self.setAxisLimits(lower=self.minResidY, upper=self.maxResidY, axis='y', updateLabel=False, target='resid', redraw=initialize)

  def toggleCrossHair(self, event):
    # toggle cross hair on middle mouse button -- cannot use QtCore.Qt.MidButton as this equates to 4?!
    if((event.button == 2) or ((event.button == 1) and event.dblclick)):
      self.cursorVisible = not self.cursorVisible
      # check whether cursor already exists
      if(self.cursor == None):
        self.cursor = MyCursor(self.ax, useblit=True, color='black', linewidth=1)

      self.cursor.toggleVisibility(self.cursorVisible, event)
    
  def destructAboutLogo(self):
    # destroys about logo
    counter = self.dataplotwidget.getDestructionCounter()
    if(counter >= 0):
      counter -= 1
      self.dataplotwidget.setDestructionCounter(np.max((counter, 0)))
      if((counter <= 0) and (len(self.handlesAbout))):
        for entry in self.handlesAbout:
          if(hasattr(entry, 'remove')):
            entry.remove()
        self.handlesAbout = []

  def drawAboutLogo(self, aspect=0, destructCounter=1):
    # draws program info on canvas
    # helper function that transforms coordinates according to axis settings
    def processCoordSet(coords, minX, maxX, modeX, minY, maxY, modeY, relWidth, relHeight, relOffsetX, relOffsetY):
      coords /= 100.0
      # process X coords
      if(modeX == 'linear'):
        coords[:,0] *= (maxX - minX) * relWidth
        coords[:,0] += minX + (maxX - minX) * relOffsetX
      else:
        minX, maxX = np.log(minX), np.log(maxX)
        coords[:,0] *= (maxX - minX) * relWidth
        coords[:,0] += minX + (maxX - minX) * relOffsetX
        coords[:,0] = np.exp(coords[:,0])
      # process Y coords
      if(modeY == 'linear'):
        coords[:,1] *= (maxY - minY) * relHeight
        coords[:,1] += minY + (maxY - minY) * relOffsetY
      else:
        minY, maxY = np.log(minY), np.log(maxY)
        coords[:,1] *= (maxY - minY) * relHeight
        coords[:,1] += minY + (maxY - minY) * relOffsetY
        coords[:,1] = np.exp(coords[:,1])
      return coords

    # helper function that transforms coordinates according to axis settings
    def processCoordSingle(minX, maxX, modeX, minY, maxY, modeY, relOffsetX, relOffsetY):
      # process X coords
      if(modeX == 'linear'):
        x = minX + (maxX - minX) * relOffsetX
      else:
        minX, maxX = np.log(minX), np.log(maxX)
        x = minX + (maxX - minX) * relOffsetX
        x = np.exp(x)
      # process Y coords
      if(modeY == 'linear'):
        y = minY + (maxY - minY) * relOffsetY
      else:
        minY, maxY = np.log(minY), np.log(maxY)
        y = minY + (maxY - minY) * relOffsetY
        y = np.exp(y)
      return [x, y]
    
    # check whether a previous logo is still displayed?
    if(not len(self.handlesAbout)):
      # settings
      zOffset = 1e3
      ubtCol = [0.011, 0.541, 0.384, 1.0]
      greyCol = [0.3, 0.3, 0.3, 1.0]
      blackCol = [0.0, 0.0, 0.0, 1.0]
      
      # retrieve axis info
      minX, maxX = self.minX, self.maxX
      minY, maxY = self.minY, self.maxY
      modeX, modeY = self.modeX, self.modeY

      # no aspect ratio specified, calculate own (don't do on first call since widgets have not resized properly yet)      
      currWidth, currHeight = self.matplot.get_size_inches()
      if(not aspect):
        aspect = currWidth / currHeight
        if(currWidth  < 10.0):
          scaleFont = currWidth / 10.0
        else:
          scaleFont = 1.0
      else:
        scaleFont = 1.0
      
      # define coordinate sets for graphics ...
      coords0 = np.array([[0.0, 0.0], [0.0, 100.0], [100.0, 100.0], [100.0, 0.0]])
      coords1 = np.array([[4.72, 4.11], [4.72, 95.13], [35.00, 95.13], [35.00, 34.76]])
      coords2 = np.array([[4.72, 4.11], [72.58, 72.14], [95.03, 72.14], [95.03, 49.53], [49.61, 4.11]])
      coords3 = np.array([[0.0, 0.0], [0.0, 100.0], [100.0, 100.0], [100.0, 0.0]])
      # ... and process them
      scaleWidth = 1
      scaleHeight = 1 / aspect
      scaleMin = np.min((scaleWidth, scaleHeight))
      scaleHeight = np.min((2.5, scaleHeight))
      scaleHeight = np.max((1.0, scaleHeight))
      widthBox = 0.8 * scaleWidth
      heightBox = 0.5 * scaleHeight
      coords0 = processCoordSet(coords0, minX, maxX, modeX, minY, maxY, modeY, widthBox, heightBox, 0.1, (1 - heightBox) / 2.0)
      coords1 = processCoordSet(coords1, minX, maxX, modeX, minY, maxY, modeY, 0.1 * scaleMin, 0.1 * scaleMin * aspect, 0.12, 0.62)
      coords2 = processCoordSet(coords2, minX, maxX, modeX, minY, maxY, modeY, 0.1 * scaleMin, 0.1 * scaleMin * aspect, 0.12, 0.62)
      coords3 = processCoordSet(coords3, minX, maxX, modeX, minY, maxY, modeY, 0.1 * scaleMin, 0.1 * scaleMin * aspect, 0.12, 0.62)
  
      # calculate coords for text labels
      text0 = processCoordSingle(minX, maxX, modeX, minY, maxY, modeY, 0.5, 0.64)
      text1 = processCoordSingle(minX, maxX, modeX, minY, maxY, modeY, 0.5, 0.45)
      text2 = processCoordSingle(minX, maxX, modeX, minY, maxY, modeY, 0.5, 0.35)
  
      # draw the background
      polyPatch0 = matplotlib.patches.Polygon(coords0, closed=True, facecolor=[1.0, 1.0, 1.0, 0.7],\
        edgecolor = greyCol, linestyle='solid', linewidth=1.0, zorder=zOffset)
      retv = self.ax.add_patch(polyPatch0)
      self.handlesAbout.append(retv)
      zOffset += 1
      
      # draw UBT logo
      polyPatch1 = matplotlib.patches.Polygon(coords1, closed=True, facecolor=[1.0]*4,\
        edgecolor = blackCol, linestyle='solid', linewidth=0.5, zorder=zOffset)
      retv = self.ax.add_patch(polyPatch1)
      self.handlesAbout.append(retv)
      zOffset += 1
  
      polyPatch2 = matplotlib.patches.Polygon(coords2, closed=True, facecolor=ubtCol,\
        edgecolor = 'None', linestyle='solid', linewidth=0.0, zorder=zOffset)
      retv = self.ax.add_patch(polyPatch2)
      self.handlesAbout.append(retv)
      zOffset += 1
  
      polyPatch3 = matplotlib.patches.Polygon(coords3, closed=True, facecolor='None',\
        edgecolor = blackCol, linestyle='solid', linewidth=0.5, zorder=zOffset)
      retv = self.ax.add_patch(polyPatch3)
      self.handlesAbout.append(retv)
      zOffset += 1
  
      # print some information
      # according to docu, positional argument would be 'text' but Matplotlib wants 's' => better don't use positional arguments
      #retv = self.ax.text(x=self.minX + 0.5 * width, y=self.minY + 0.5 * height, s='Fit-o-mat',\
      #  horizontalalignment='center', zorder=zOffset)
      retv = self.ax.text(text0[0], text0[1], 'Fit-o-mat',\
        horizontalalignment='center', zorder=zOffset, style='normal', fontsize=scaleFont * scaledDPI(14),\
        fontweight='bold', color=ubtCol)
      self.handlesAbout.append(retv)
      zOffset += 1
      
      retv = self.ax.text(text1[0], text1[1],\
        '\u00A9' + ' by A.M. 2017-2018\nandreas.moeglich@uni-bayreuth.de\nGNU General Public License v3.0',\
        horizontalalignment='center', zorder=zOffset, style='normal', fontsize=scaleFont * scaledDPI(9),\
        fontweight='normal', color=greyCol)
      self.handlesAbout.append(retv)
      zOffset += 1
      
      retv = self.ax.text(text2[0], text2[1], 'version '+ VERSION, horizontalalignment='center', zorder=zOffset,\
        style='italic', fontsize=scaleFont * scaledDPI(7), fontweight='normal', color=greyCol)
      self.handlesAbout.append(retv)
      zOffset += 1
    else:
      self.dataplotwidget.setDestructionCounter(1)
      self.destructAboutLogo()
      destructCounter = 0
      
    # refresh the plot to draw everything
    self.dataplotwidget.myRefresh()
    
    # set us up for ready destruction
    self.dataplotwidget.setDestructionCounter(destructCounter)

  def initLegend(self):
    # initializes legend (has to occur after function is drawn)
    self.setLegend(value=self.legendVisible, redraw=False, target='plot')
    self.setLegendPlacement(value=self.legendPlacement, redraw=False, target='plot')
    for prop in ['face', 'edge']:
      self.setLegendColor(value=self.legendColor[prop], prop=prop, redraw=False, target='plot')
    self.setLegendEdgeWidth(value=self.legendEdgeWidth, redraw=False, target='plot')
    self.setLegendShadow(value=self.legendShadow, redraw=False, target='plot')
    self.setLegendLabelColor(value=self.legendLabelColor, redraw=False, target='plot')
    self.setLegendLabelSize(value=self.legendLabelSize, redraw=False, target='plot')
    self.setLegendLabelFont(value=self.legendLabelFont, redraw=False, target='plot')
   
  def changeAxisLimits(self, axis='x', target='plot', redraw=True):
    # check whether to operate on data or resid plot
    if(target in ['plot', 'resid']):
      # changes limits of axis
      if(axis == 'x'):
        # retrieve values from field
        upperx = self.upperLimitx.text()
        try:
          upperx = float(upperx)
        except:
          upperx = 0.0
  
        lowerx = self.lowerLimitx.text()
        try:
          lowerx = float(lowerx)
        except:
          lowerx = 0.0
        # check whether any value changed
        if((upperx != self.maxX) or (lowerx != self.minX)):
          # do some checks and update axis (don't redraw, plot functions will take care of)
          self.setAxisLimits(lower = lowerx, upper = upperx, axis = 'x', updateLabel = False, target='plot', redraw=False)
          self.setAxisLimits(lower = lowerx, upper = upperx, axis = 'x', updateLabel = False, target='resid', redraw=False)
          # replot function over current x-interval
          if(self.modeX == 'linear'):
            plot_interval = np.linspace(self.minX, self.maxX, self.DATAPOINTS_SIMULATION)
          elif(self.modeX == 'log'):
            plot_interval = np.linspace(np.log(self.minX), np.log(self.maxX), self.DATAPOINTS_SIMULATION)
            plot_interval = np.exp(plot_interval)
            
          self.parent.fit[self.parent.activeFit].handlePlot = self.plotFunction(\
            fitobject = self.parent.fit[self.parent.activeFit], x = plot_interval,\
            handlePlot = self.parent.fit[self.parent.activeFit].handlePlot, redraw=redraw)
          self.handleResidZero = self.plotResidZero(handleResidZero=self.handleResidZero, redraw=redraw)
      elif(axis == 'y'):
        # retrieve values from field
        if(target == 'plot'):
          uppery = self.upperLimity.text()
          lowery = self.lowerLimity.text()
        else:
          uppery = self.upperLimitResidy.text()
          lowery = self.lowerLimitResidy.text()

        try:
          uppery = float(uppery)
        except:
          uppery = 0.0
  
        try:
          lowery = float(lowery)
        except:
          lowery = 0.0
        
        # check whether any value changed
        if(target == 'plot'):
          if((uppery != self.maxY) or (lowery != self.minY)):
            # do some checks and update axis
            self.setAxisLimits(lower = lowery, upper = uppery, axis = 'y', updateLabel = False, target=target, redraw=redraw)
        else:
          if((uppery != self.maxResidY) or (lowery != self.minResidY)):
            # do some checks and update axis
            self.setAxisLimits(lower = lowery, upper = uppery, axis = 'y', updateLabel = False, target=target, redraw=redraw)
      
  def setAxisLimits(self, lower=0, upper=1, axis='x', updateLabel=False, target='plot', redraw=True):
    if(target in ['plot', 'resid']):
      if(target == 'plot'):
        plotobject = self.dataplotwidget; axisobject = self.ax
      else:
        plotobject = self.residplotwidget; axisobject = self.ax_resid
    else:
      axis='abort'
    # performs checks and then sets axis limits
    if(axis == 'x'):
      self.minX = lower; self.maxX = upper
      # check current axis mode and take care of log values
      axis_mode = str(self.modeSelectorx.currentText())
      if (axis_mode == 'log'):
        if ((self.minX <= 0) or (self.maxX <= 0)):
          # look whether data are loaded
          data = self.parent.data[self.parent.activeData].value()
          if ('x' in data):
            xdata = np.array(data['x'])
            xdata = xdata[xdata > 0]
            if(len(xdata)):
              min_xdata = np.min(xdata); max_xdata = np.max(xdata)
              if((self.data_spacer > 0) and (len(xdata) > 1)):
                difference = np.log(max_xdata / min_xdata)
                min_xdata = np.exp(np.log(min_xdata) - self.data_spacer * difference)
                max_xdata = np.exp(np.log(max_xdata) + self.data_spacer * difference)
            else:
              min_xdata, max_xdata = 0, 0
            self.minX = np.max((self.EPSILON, self.minX, min_xdata))
            self.maxX = np.max((self.EPSILON, self.maxX, max_xdata))
          else:
            # ensure that min and max values are positive
            self.minX = np.max((self.EPSILON, self.minX))
            self.maxX = np.max((self.EPSILON, self.maxX))
          updateLabel = True
      
      # update labels?
      if(updateLabel):
        self.upperLimitx.setText(str(self.parent.formatNumber(self.maxX)))
        self.lowerLimitx.setText(str(self.parent.formatNumber(self.minX)))
        
      # update axis
      axisobject.set_xlim([self.minX, self.maxX])
      if(redraw):
        plotobject.myRefresh()
    elif(axis == 'y'):
      if(target == 'plot'):
        self.minY = lower; self.maxY = upper
        # check current axis mode and take care of log values
        axis_mode = str(self.modeSelectory.currentText())
        if ((axis_mode == 'log') and (target == 'plot')):
          if ((self.minY <= 0) or (self.maxY <= 0)):
            # look whether data are loaded
            data = self.parent.data[self.parent.activeData].value()
            if ('y' in data):
              ydata = np.array(data['y'])
              ydata = ydata[ydata > 0]
              if(len(ydata)):
                min_ydata = np.min(ydata); max_ydata = np.max(ydata)
                if((self.data_spacer > 0) and (len(ydata) > 1)):
                  difference = np.log(max_ydata / min_ydata)
                  min_ydata = np.exp(np.log(min_ydata) - self.data_spacer * difference)
                  max_ydata = np.exp(np.log(max_ydata) + self.data_spacer * difference)
              else:
                min_ydata, max_ydata = 0, 0
              self.minY = np.max((self.EPSILON, self.minY, min_ydata))
              self.maxY = np.max((self.EPSILON, self.maxY, max_ydata))
            else:
              # ensure that min and max values are positive
              self.minY = np.max((self.EPSILON, self.minY))
              self.maxY = np.max((self.EPSILON, self.maxY))
            updateLabel = True
        
        # update labels?
        if(updateLabel):
          self.upperLimity.setText(str(self.parent.formatNumber(self.maxY)))
          self.lowerLimity.setText(str(self.parent.formatNumber(self.minY)))

        # update axis
        axisobject.set_ylim([self.minY, self.maxY])
        if(redraw):
          plotobject.myRefresh()
      else:
        self.minResidY = lower; self.maxResidY = upper

        # update labels?
        if(updateLabel):
            self.upperLimitResidy.setText(str(self.parent.formatNumber(self.maxResidY)))
            self.lowerLimitResidy.setText(str(self.parent.formatNumber(self.minResidY)))
        
        # update axis
        #print('yelp', self.minResidY, self.maxResidY)
        axisobject.set_ylim([self.minResidY, self.maxResidY])
        if(redraw):
          plotobject.myRefresh()
    
  def changeAxisMode(self, axis='x', redraw=True):
    # changes scale mode of axis
    if(axis == 'x'):
      # adjust axis
      axis_mode = str(self.modeSelectorx.currentText())
      self.setAxisLimits(lower = self.minX, upper = self.maxX, axis = 'x', updateLabel = False, target='plot', redraw=False)
      self.ax.set_xscale(axis_mode)
      self.setAxisLimits(lower = self.minX, upper = self.maxX, axis = 'x', updateLabel = False, target='resid', redraw=False)
      self.ax_resid.set_xscale(axis_mode)
      self.modeX = axis_mode
      # trigger redrawing of fit function with new axis limits
      if(self.modeX == 'linear'):
        plot_interval = np.linspace(self.minX, self.maxX, self.DATAPOINTS_SIMULATION)
      elif(self.modeX == 'log'):
        plot_interval = np.linspace(np.log(self.minX), np.log(self.maxX), self.DATAPOINTS_SIMULATION)
        plot_interval = np.exp(plot_interval)
        
      self.parent.fit[self.parent.activeFit].handlePlot = self.plotFunction(\
        fitobject = self.parent.fit[self.parent.activeFit], x = plot_interval,\
        handlePlot = self.parent.fit[self.parent.activeFit].handlePlot, redraw=False)
      self.handleResidZero = self.plotResidZero(handleResidZero=self.handleResidZero, redraw=False)
      # redraw
      if(redraw):
        self.dataplotwidget.myRefresh()
        self.residplotwidget.myRefresh()
    elif(axis == 'y'):
      # adjust axis
      axis_mode = str(self.modeSelectory.currentText())
      self.setAxisLimits(lower = self.minY, upper = self.maxY, axis = 'y', updateLabel = False, redraw=False)
      self.ax.set_yscale(axis_mode)
      self.modeY = axis_mode
      # redraw
      if(redraw):
        self.dataplotwidget.myRefresh()

  def plotResidZero(self, handleResidZero=None, redraw=False):
    # plots zero line in residuals plot
    self.handleResidZero = handleResidZero
    # set up data
    xval = [self.minX, self.maxX]
    yval = [0, 0]
    # do the actual plot
    if(self.handleResidZero != None):
      #self.handleData.remove()
      self.handleResidZero.set_xdata(xval)
      self.handleResidZero.set_ydata(yval)
    else:
      self.handleResidZero, = self.ax_resid.plot(xval, yval, 'ko', zorder = 0.5  + self.parent.zOffset)
    self.rememberSettingResidLine['init'] = 'ax_resid.plot(' + repr(xval) + ', ' + repr(yval) + ', zorder=' + repr(0.5  + self.parent.zOffset) + ')'
      
    # apply style of fit curve to zero line
    style = self.parent.data[self.parent.activeData].getResidLineStyle()
    for key in style:
      method = 'set_'+key
      if (hasattr(self.handleResidZero, method)):
        method2call = getattr(self.handleResidZero, method)
        method2call(style[key])
        self.rememberSettingResidLine[key] = 'set_' + key + '(' + repr(style[key]) + ')'
    # ensure only line is visible but not markers
    if (hasattr(self.handleResidZero, 'set_linestyle')):
        method2call = getattr(self.handleResidZero, 'set_linestyle')
        method2call('solid')        
        self.rememberSettingResidLine['linestyle'] = 'set_linestyle(\'solid\')'
    if (hasattr(self.handleResidZero, 'set_marker')):
        method2call = getattr(self.handleResidZero, 'set_marker')
        method2call('None')
        self.rememberSettingResidLine['marker'] = 'set_marker(\'None\')'
        
    # do redraw?
    if(redraw):
      self.residplotwidget.myRefresh()
    
    return self.handleResidZero

  def plotResid(self, dataobject=None, handleResid=None, handleResidZero=None, redraw=True):
    # assign handles
    self.handleResid = handleResid
    self.handleResidZero = handleResidZero
      
    # was dataobject specified?
    if(dataobject == None):
      dataobject = self.parent.data[self.parent.activeData]
    
    # analyze data
    xval = dataobject.x
    yval = dataobject.resid
    if(yval.size > 0):
      # plot residuals
      if(self.handleResid != None):
        self.handleResid.set_xdata(xval)
        self.handleResid.set_ydata(yval)
      else:
        self.handleResid, = self.ax_resid.plot(xval, yval, 'ko', zorder = dataobject.zorder + self.parent.zOffset)
        
      # apply styles
      style = dataobject.getResidStyle()
      for key in style:
        method = 'set_'+key
        if (hasattr(self.handleResid, method)):
          method2call = getattr(self.handleResid, method)
          method2call(style[key])

      # plot zero line
      self.handleResidZero = self.plotResidZero(self.handleResidZero, False)
          
      # adjust x-axis limits to those of main plot
      self.setAxisLimits(lower = self.minX, upper = self.maxX, axis = 'x', updateLabel = False, target='resid', redraw=False)
      
      # auto adjust y limits
      # need to take care of potential nan and inf values
      procval = [i for i in yval if ((not np.isnan(i)) and (not np.isinf(i)))]
      if(len(procval)):
        temp_ylimit = np.max([np.abs(i) for i in procval])
        # ensure minimum limit
        if (temp_ylimit == 0):
          self.maxResidY = self.EPSILON; self.minResidY = -self.EPSILON
        else:
          self.maxResidY = 1.2 * temp_ylimit; self.minResidY = -1.2 * temp_ylimit
        self.setAxisLimits(lower = self.minResidY, upper = self.maxResidY, axis = 'y', updateLabel = True, target='resid', redraw=False)

      # draw everything
      if(redraw):
        self.residplotwidget.myRefresh()

      return self.handleResid, self.handleResidZero
    else:
      if(self.handleResid != None):
        self.handleResid.remove()
      return None, self.handleResidZero
    
  def plotData(self, data, dataobject=None, handleData=None, handleErr=None, handleBar=None, handleStack=None, redraw=True, rescale=True):
    # assign handles
    self.handleData = handleData
    self.handleErr = handleErr
    self.handleBar = handleBar
    self.handleStack = handleStack

    # was dataobject specified?
    if(dataobject == None):
      dataobject = self.parent.data[self.parent.activeData]
      
    # analyze data
    xerr, yerr = np.array([]), np.array([])
    if (('x' in data) and ('y' in data)):
      # okay found valid data, now assign values
      xval = data['x']
      yval = data['y']
      
      if ('xerr' in data):
        xerr = data['xerr']
        
      if ('yerr' in data):
        yerr = data['yerr']
        
      # can do some plotting
      if(self.handleData != None):
        self.handleData.set_xdata(xval)
        self.handleData.set_ydata(yval)
      else:
        self.handleData, = self.ax.plot(xval, yval, 'ko', zorder = dataobject.zorder  + self.parent.zOffset)
      
      # draw bar?
      if(self.handleBar != None):
        self.handleBar.remove()

      if((dataobject.Barstyle['showBar']) and (dataobject.Barstyle['offset'] != 0)):
        # also use this for error bars
        useOffset = dataobject.Barstyle['offset']
      else:
        useOffset = 0
  
      if(dataobject.Barstyle['showBar']):
        barstyle = dataobject.getBarStyle()
        if('width' in barstyle):
          usewidth = barstyle['width']
        else:
          usewidth = 0.5

        self.handleBar = self.ax.bar(xval + useOffset, yval, zorder=dataobject.zorder + dataobject.relativeZOrderBar + self.parent.zOffset, align='center', width=usewidth)
      else:
        self.handleBar = None

      # draw stack?
      if(self.handleStack != None):
        self.handleStack.remove()

      if(dataobject.Stackstyle['showStack']):
        self.handleStack, = self.ax.stackplot(xval, yval, zorder=dataobject.zorder + dataobject.relativeZOrderBar + self.parent.zOffset)
      else:
        self.handleStack = None

      # draw error bars?
      if (self.handleErr != None):
        self.handleErr[0].remove()
        for entry in self.handleErr[1]:
          entry.remove()
        for entry in self.handleErr[2]:
          entry.remove()
          
      if(xerr.size):
        if(yerr.size):
          self.handleErr = self.ax.errorbar(xval + useOffset, yval, xerr = xerr, yerr = yerr, zorder = dataobject.zorder + dataobject.relativeZOrderError + self.parent.zOffset, capsize = 1)#, fmt = 'o')
        else:
          self.handleErr = self.ax.errorbar(xval + useOffset, yval, xerr = xerr, zorder = dataobject.zorder + dataobject.relativeZOrderError + self.parent.zOffset, capsize = 1)#, fmt = 'o')
      elif(yerr.size):
        self.handleErr = self.ax.errorbar(xval + useOffset, yval, yerr = yerr, zorder = dataobject.zorder + dataobject.relativeZOrderError  + self.parent.zOffset, capsize = 1)#, fmt = 'o')
      else:
        self.handleErr = None
      
      if(self.handleErr != None):
        # don't draw the error curve
        self.handleErr[0].set_linestyle('None')
        self.handleErr[0].set_marker('None')
      
      # adjust axis limits
      if((self.autoScaleX) and (rescale)):
        if(xerr.size):
          temp_xmin = np.min([i-j for i, j in zip(xval, xerr)])
          temp_xmax = np.max([i+j for i, j in zip(xval, xerr)])
        else:
          temp_xmin = np.min(xval)
          temp_xmax = np.max(xval)
          
        # ensure minimum limit
        if (temp_xmax - temp_xmin < self.EPSILON):
          temp_xmax += self.EPSILON; temp_xmin -= self.EPSILON
        elif(self.data_spacer > 0):
          if(self.modeX == 'linear'):
            difference = temp_xmax - temp_xmin
            temp_xmax += difference * self.data_spacer
            temp_xmin -= difference * self.data_spacer
          else:
            # log scale -- isolate positive data
            pos_x = np.array(xval)
            pos_x = pos_x[pos_x > 0]
            # recalc. xmin to address error when restoring state
            temp_xmin = np.min(pos_x)
            if(len(pos_x > 1)):
              difference = np.log(pos_x[-1] / pos_x[0])
              temp_xmin = np.exp(np.log(temp_xmin) - self.data_spacer * difference)
              temp_xmax = np.exp(np.log(temp_xmax) + self.data_spacer * difference)
              
        self.setAxisLimits(lower = temp_xmin, upper = temp_xmax, axis = 'x', updateLabel = True, redraw=False)
        
      if((self.autoScaleY) and (rescale)):
        if(yerr.size):
          temp_ymin = np.min([i-j for i, j in zip(yval, yerr)])
          temp_ymax = np.max([i+j for i, j in zip(yval, yerr)])
        else:
          temp_ymin = np.min(yval)
          temp_ymax = np.max(yval)
  
        # ensure minimum limit
        if (temp_ymax-temp_ymin<self.EPSILON):
          temp_ymax += self.EPSILON; temp_ymin -= self.EPSILON
        elif(self.data_spacer > 0):
          if(self.modeY == 'linear'):
            difference = temp_ymax - temp_ymin
            temp_ymax += difference * self.data_spacer
            temp_ymin -= difference * self.data_spacer
          else:
            # log scale -- isolate positive data
            pos_y = np.array(yval)
            pos_y = pos_y[pos_y > 0]
            if(len(pos_y > 1)):
              difference = np.log(pos_y[-1] / pos_y[0])
              temp_ymin = np.exp(np.log(temp_ymin) - self.data_spacer * difference)
              temp_ymax = np.exp(np.log(temp_ymax) + self.data_spacer * difference)

        self.setAxisLimits(lower = temp_ymin, upper = temp_ymax, axis = 'y', updateLabel = True, redraw=False)
      
      # apply styles
      style = dataobject.getStyle()
      for key in style:
        method = 'set_'+key
        if (hasattr(self.handleData, method)):
          method2call = getattr(self.handleData, method)
          method2call(style[key])
          
      # apply styles to error bars
      if (self.handleErr != None):
        errorstyle = dataobject.getErrorStyle()
        # Note: self.handleErr[1] are the caps, self.handleErr[2] are the lines (super confusing!!)
        for key in errorstyle:
          method = 'set_'+key
          for entry in self.handleErr[1]:
            if (hasattr(entry, method)):
              method2call = getattr(entry, method)
              method2call(errorstyle[key])
          for entry in self.handleErr[2]:
            if (hasattr(entry, method)):
              method2call = getattr(entry, method)
              method2call(errorstyle[key])
        # don't connect caps of error bars
        for entry in self.handleErr[1]:
          entry.set_linestyle('None')
      
      # set name
      if (hasattr(self.handleData, 'set_label')):
        method2call = getattr(self.handleData, 'set_label')
        method2call(dataobject.name)
        
      # apply bar styles
      if(dataobject.Barstyle['showBar']):
        barstyle = dataobject.getBarStyle()
        for entry in self.handleBar.patches:
          for key in barstyle:
            method = 'set_'+key
            # treat width differently to avoid recentering of bars upon width change (does not heed center position)
            if ((key != 'width') and (hasattr(entry, method))):
              method2call = getattr(entry, method)
              method2call(barstyle[key])
        # check visibility of entire object
        if(not dataobject.visibility):
          for entry in self.handleBar.patches:
            entry.set_visible(False)
  
      # apply stack styles
      if(dataobject.Stackstyle['showStack']):
        stackstyle = dataobject.getStackStyle()
        for key in stackstyle:
          method = 'set_'+key
          if (hasattr(self.handleStack, method)):
            method2call = getattr(self.handleStack, method)
            method2call(stackstyle[key])
        # check visibility of entire object
        if(not dataobject.visibility):
          self.handleStack.set_visible(False)
  
      # draw everything
      if(redraw):
        self.dataplotwidget.myRefresh()
      
    # return handles to graphics objects
    return self.handleData, self.handleErr, self.handleBar, self.handleStack
      
  def plotFunction(self, fitobject=None, x=[], handlePlot=None, redraw=True):
    # retrieve plot handle
    self.handlePlot = handlePlot
    
    # was fitobject specified?
    if(fitobject == None):
      fitobject = self.parent.fit[self.parent.activeFit]
    
    # was target plot interval specified?
    if (len(x)):
      self.x = np.array(x)
    else:
      # determine x interval of plot
      xmin, xmax = self.minX, self.maxX
      if(self.modeX == 'linear'):
        self.x = np.linspace(xmin, xmax, self.DATAPOINTS_SIMULATION)
      elif(self.modeX == 'log'):
        self.x = np.linspace(np.log(xmin), np.log(xmax), self.DATAPOINTS_SIMULATION)
        self.x = np.exp(self.x)
    
    # calculate function values
    self.x, self.y = fitobject.simulateFunc(self.x)
    # can do some plotting
    if(self.handlePlot != None):
      self.handlePlot.set_xdata(self.x)
      self.handlePlot.set_ydata(self.y)
    else:
      self.handlePlot, = self.ax.plot(self.x, self.y, zorder = fitobject.zorder + self.parent.zOffset)
      
    # adjust y limits
    if(self.autoScaleY):
      # check if data is loaded
      if('y' in self.parent.data[self.parent.activeData].value()):
        temp_data = self.parent.data[self.parent.activeData].value()
        temp_y = np.hstack((self.y, temp_data['y']))
      else:
        temp_y = self.y

      temp_y = temp_y[np.isfinite(temp_y)]
      temp_ymin = np.min(temp_y)
      temp_ymax = np.max(temp_y)
        
      if(temp_ymax-temp_ymin<self.EPSILON):
        temp_ymax += self.EPSILON; temp_ymin -= self.EPSILON
      elif(self.data_spacer > 0):
        if(self.modeY == 'linear'):
          difference = temp_ymax - temp_ymin
          temp_ymax += difference * self.data_spacer
          temp_ymin -= difference * self.data_spacer
        else:
          # log scale -- isolate positive data
          pos_y = np.array(temp_y)
          pos_y = pos_y[pos_y > 0]
          if(len(pos_y > 1)):
            difference = np.log(pos_y[-1] / pos_y[0])
            temp_ymin = np.exp(np.log(temp_ymin) - self.data_spacer * difference)
            temp_ymax = np.exp(np.log(temp_ymax) + self.data_spacer * difference)

      self.setAxisLimits(lower = temp_ymin, upper = temp_ymax, axis = 'y', updateLabel = True, redraw=False)
    
    # apply styles
    style = fitobject.getStyle()
    for key in style:
      method = 'set_'+key
      if (hasattr(self.handlePlot, method)):
        method2call = getattr(self.handlePlot, method)
        method2call(style[key])
      
    # set name
    if (hasattr(self.handlePlot, 'set_label')):
      method2call = getattr(self.handlePlot, 'set_label')
      method2call(fitobject.name)

    # and finally draw everything
    if(redraw):
      self.dataplotwidget.myRefresh()

    # return handles to graphics
    return self.handlePlot

class BruteWindow(QtWidgets.QMainWindow):
  def __init__(self, parent=None, title=' '):
    super(BruteWindow, self).__init__()
    self.parent = parent
    self.title = title
    self.setWindowTitle(self.title)
    
    self.centralwidget = QWidgetMac(self)
    self.centralwidget.setMinimumSize(QtCore.QSize(scaledDPI(250), scaledDPI(100)))
    self.centralwidget.setMaximumSize(QtCore.QSize(scaledDPI(250), scaledDPI(100)))
    self.setCentralWidget(self.centralwidget)
    
    self.vLayout = QtWidgets.QVBoxLayout(self.centralwidget)
    self.vLayout.setAlignment(QtCore.Qt.AlignCenter|QtCore.Qt.AlignTop)
    self.vLayout.setContentsMargins(0, 0, 0, 0)
    
    self.messageLabel = QtWidgets.QLabel()
    self.vLayout.addWidget(self.messageLabel)

    self.messageLabel2 = QtWidgets.QLabel()
    self.vLayout.addWidget(self.messageLabel2)

    self.messageLabel3 = QtWidgets.QLabel()
    self.vLayout.addWidget(self.messageLabel3)

    self.messageLabel4 = QtWidgets.QLabel()
    self.vLayout.addWidget(self.messageLabel4)

    self.closeButton = QPushButtonMac()
    self.closeButton.setText('Stop')
    self.closeButton.clicked.connect(self.close)
    self.vLayout.addWidget(self.closeButton)
    
  def closeEvent(self,event):
    # stop fit procedure in parent window
    self.parent.runFlag = False

# a custom QTextEdit
class myQTextEdit(QtWidgets.QTextEdit):
  def __init__(self, parent = None):
    super(myQTextEdit, self).__init__(parent)
    self._originalFocusInEvent = QtWidgets.QTextEdit.focusInEvent
    self.parent = parent
    # for some reason need to explicitly set QSTYLE again -- could be due to nested widgets?! unclear
    if(QSTYLE != None):
      self.setStyle(QSTYLE)

  def focusInEvent(self, event):
    self._originalFocusInEvent(self, event)
    # don't use palettes as these are incompatible with style sheets
    self.setStyleSheet('myQTextEdit {background-color: white;}')
    
  def keyPressEvent(self, event):
    if event.matches(QtGui.QKeySequence.Save):
      if(self.parent != None):
        self.parent.saveFit()
    elif event.matches(QtGui.QKeySequence.Open):
      # pass through event
      event.ignore()
    else:
      QtWidgets.QTextEdit.keyPressEvent(self, event)
      # prevent event from triggering main ui as well
      event.accept()
      
class FitArea(QWidgetMac):
  def __init__(self, parent=None):
    super(FitArea, self).__init__()
    self.parent = parent
    self.validFloat = QtGui.QDoubleValidator()
    self.param = []
    self.confidence = []
    self.param_active = []
    self.ffuncList = self.initFfunc(path=WORKINGDIR + PATH_SEPARATOR + 'functions' + PATH_SEPARATOR)
    self.fitResultsHeader = 'Latest fit results:'
    self.fitResultsHeader += '\n' + '-' * len(self.fitResultsHeader) + '\n'
    self.outstring = self.fitResultsHeader
    # use epsilon as minimum error value and for calculating derivatives
    self.EPSILON = 1e-9
    # define amplitude threshold for random variation of parameters
    self.MIN_AMPLITUDE = 0.5
    
    # set up GUI
    self.buildRessource()

  def buildRessource(self):
    self.vLayout = QtWidgets.QVBoxLayout(self)
    
    # set up Shrink-O-tainer for fit formula
    self.fitFunctionContainer = ShrinkoWidget(container=self, factor=0.5, offset=0.0)
    self.vLayout.addWidget(self.fitFunctionContainer)
    self.LayoutFitFunctionContainer = QtWidgets.QVBoxLayout(self.fitFunctionContainer)
    self.LayoutFitFunctionContainer.setContentsMargins(0, 0, 0, 0)

    # set up selector for fit functions
    self.comboBox = QComboBoxMac()
    self.comboBox.setMinimumHeight(scaledDPI(BASE_SIZE))
    self.comboBox.setMaximumHeight(scaledDPI(BASE_SIZE))
    self.LayoutFitFunctionContainer.addWidget(self.comboBox)
    self.populateFfuncSelector()
    self.comboBox.activated.connect(self.selectFfunc)

    # set up field that declares parameters
    self.declareParamBox = QWidgetMac()
    self.hLayout = QtWidgets.QHBoxLayout(self.declareParamBox)
    self.hLayout.setContentsMargins(0, 0, 0, 0)
    self.declareParamLabel = QtWidgets.QLabel()
    self.declareParamLabel.setText('Parameters')
    self.declareParamLabel.setMinimumSize(QtCore.QSize(scaledDPI(65), scaledDPI(20)))
    self.declareParamLabel.setMaximumSize(QtCore.QSize(scaledDPI(65), scaledDPI(20)))
    self.hLayout.addWidget(self.declareParamLabel)
    self.declareParamEntry = QLineEditClick()
    self.declareParamEntry.setMinimumHeight(scaledDPI(BASE_SIZE))
    self.declareParamEntry.setMaximumHeight(scaledDPI(BASE_SIZE))
    self.hLayout.addWidget(self.declareParamEntry)
    
    self.LayoutFitFunctionContainer.addWidget(self.declareParamBox)
    
    # set up edit field for fit function
    self.fitFormula = myQTextEdit(self)
    self.fitFormula.setLineWrapMode(QtWidgets.QTextEdit.NoWrap)
    self.fitFormula.setGeometry(QtCore.QRect(0, 0, scaledDPI(500), scaledDPI(600)))
    self.LayoutFitFunctionContainer.addWidget(self.fitFormula)

    # read all available fit functions
    if (len(self.ffuncList)):
      success, parameters, formula, values, active = self.loadFfunc(self.ffuncList[0])
      self.paramList = parameters
      parameters = ', '.join(parameters)
    else:
      parameters = 'A0, A1, k1'
      self.paramList = ['A0', 'A1', 'k1']
      formula = 'y = A0 + A1 * np.exp(-k1*x)'
      values = [1, 1, 1]
      active = [True] * 3

    self.declareParamEntry.setText(parameters)
    self.fitFormula.setText(formula)
    self.param = values
    self.confidence = ['--']*len(values)
    self.param_active = [1 if i else 0 for i in active]
    
    # set up buttons
    self.buttonContainer = QWidgetMac()
    self.buttonContainer.setContentsMargins(0, 0, 0, 0)
    self.LayoutFitFunctionContainer.addWidget(self.buttonContainer)
    self.LayoutButtonContainer = QtWidgets.QHBoxLayout(self.buttonContainer)
    self.LayoutButtonContainer.setContentsMargins(0, 0, 0, 0)
    
    self.saveFitButton = QPushButtonMac()
    self.saveFitButton.setText('Save Fit Function')
    self.saveFitButton.setMinimumHeight(scaledDPI(BASE_SIZE))
    self.saveFitButton.setMaximumHeight(scaledDPI(BASE_SIZE))
    self.saveFitButton.clicked.connect(self.saveFit)
    self.LayoutButtonContainer.addWidget(self.saveFitButton)
    self.useFitButton = QPushButtonMac()
    self.useFitButton.setText('Apply Fit Function')
    self.useFitButton.setMinimumHeight(scaledDPI(BASE_SIZE))
    self.useFitButton.setMaximumHeight(scaledDPI(BASE_SIZE))
    self.useFitButton.clicked.connect(partial(self.useFit, True))
    self.LayoutButtonContainer.addWidget(self.useFitButton)

    # set up Shrink-O-tainer for parameter table
    self.parameterTableContainer = ShrinkoWidget(container=self, factor=0.3, offset=0.5)
    self.vLayout.addWidget(self.parameterTableContainer)
    self.LayoutParameterTableContainer = QtWidgets.QVBoxLayout(self.parameterTableContainer)
    self.LayoutParameterTableContainer.setContentsMargins(0, 0, 0, 0)

    # set up parameter table
    blah = self.HLine()
    self.LayoutParameterTableContainer.addWidget(blah)
    self.ParamTable = QtWidgets.QTableWidget()
    self.ParamTable.setEnabled(True)
    self.ParamTable.setColumnCount(3)
    self.ParamTable.setRowCount(1)
    self.ParamTable.setHorizontalHeaderItem(0, QtWidgets.QTableWidgetItem('Fit?'))
    self.ParamTable.setHorizontalHeaderItem(1, QtWidgets.QTableWidgetItem('Value'))
    self.ParamTable.setHorizontalHeaderItem(2, QtWidgets.QTableWidgetItem('Error'))
    self.LayoutParameterTableContainer.addWidget(self.ParamTable)
    self.updateParamTable()
    self.useFit(redraw=False)
   
    # set fit controls
    self.ButtonContainer = QWidgetMac()
    self.LayoutParameterTableContainer.addWidget(self.ButtonContainer)
    self.LayoutButtonContainer = QtWidgets.QHBoxLayout(self.ButtonContainer)
    self.LayoutButtonContainer.setContentsMargins(0, 0, 0, 0)

    # set up grid search button
    self.doGridSearchButton = QPushButtonMac()
    self.doGridSearchButton.setText('Grid Search')
    self.doGridSearchButton.setMinimumHeight(scaledDPI(BASE_SIZE))
    self.doGridSearchButton.setMaximumHeight(scaledDPI(BASE_SIZE))
    self.doGridSearchButton.clicked.connect(self.doGridSearch)
    self.LayoutButtonContainer.addWidget(self.doGridSearchButton)

    # set up random fit button
    self.doBruteButton = QPushButtonMac()
    self.doBruteButton.setText('Random Search')
    self.doBruteButton.setMinimumHeight(scaledDPI(BASE_SIZE))
    self.doBruteButton.setMaximumHeight(scaledDPI(BASE_SIZE))
    self.doBruteButton.clicked.connect(self.doBruteFit)
    self.LayoutButtonContainer.addWidget(self.doBruteButton)

    # set up Fit button
    self.doFitButton = QPushButtonMac()
    self.doFitButton.setText('Fit Data')
    self.doFitButton.setMinimumHeight(scaledDPI(BASE_SIZE))
    self.doFitButton.setMaximumHeight(scaledDPI(BASE_SIZE))
    self.doFitButton.clicked.connect(self.doFit)
    self.LayoutButtonContainer.addWidget(self.doFitButton)

    # set up Shrink-O-tainer for fit results
    self.fitResultsContainer = ShrinkoWidget(container=self, factor=0.2, offset=0.8)
    self.vLayout.addWidget(self.fitResultsContainer)
    self.LayoutFitResultsContainer = QtWidgets.QVBoxLayout(self.fitResultsContainer)
    self.LayoutFitResultsContainer.setContentsMargins(0, 0, 0, 0)
    
    # set up text edit field for displaying fit results
    blah = self.HLine()
    self.LayoutFitResultsContainer.addWidget(blah)
    self.fitResults = QtWidgets.QTextEdit()
    self.fitResults.setLineWrapMode(QtWidgets.QTextEdit.NoWrap)
    self.fitResults.setGeometry(QtCore.QRect(0, 0, scaledDPI(500), scaledDPI(600)))
    self.LayoutFitResultsContainer.addWidget(self.fitResults)
    self.fitResults.setReadOnly(True)
    self.fitResults.setText(self.fitResultsHeader)
    self.parent.fit[self.parent.activeFit].fitresults = self.fitResultsHeader

  def reportState(self):
    # reports data content for saveState function
    retv = {}
    retv['parameters'] = self.paramList
    retv['formula'] = self.fitFormula.toPlainText()
    retv['fitresults'] = self.fitResults.toPlainText()
    retv['param'] = self.param
    retv['confidence'] = self.confidence
    retv['active'] = self.param_active
    
    return retv

  def restoreState(self, data):
    # restores data content from loadState function
    try:
      parameters = data['parameters']
      formula = data['formula']
      values = data['param']
      active = data['active']
      fitresults = data['fitresults']
      confidence = data['confidence']
     
      # restore fit function
      self.restoreFfunc(parameters, formula, values, active, fitresults)
      
      # additionally restore confidence
      self.confidence = confidence
      self.changeParamTable()
    except:
      self.parent.statusbar.showMessage('Failed to restore state!', self.parent.STATUS_TIME)
      print('Failed to restore state', data)

  def populateFfuncSelector(self):
    # initializes or updates function selector
    self.comboBox.clear()
    itemList = []
    
    for entry in self.ffuncList:
      menuItem = entry
      if('\\' in menuItem):
        menuItem = menuItem.split('\\')[-1]
      elif('/' in menuItem):
        menuItem = menuItem.split('/')[-1]
      menuItem = menuItem.split('.')[0]
      itemList.append(menuItem)
    
    # sort itemList
    if(len(itemList)):
      itemList, self.ffuncList = [list(i) for i in zip(*sorted(zip(itemList, self.ffuncList), key=lambda s: s[0].lower()))]
    
    #for menuItem in sorted(itemList):
    for menuItem in itemList:
      self.comboBox.addItem(menuItem)

  def saveFit(self):
    # saves fit function
    # determine currently selected function
    index = self.comboBox.currentIndex()
    if(index + 1):
      currFunc = self.ffuncList[index]
    else:
      currFunc = '.'
    
    # open save dialog
    saveDialog = QtWidgets.QFileDialog()
    saveDialog.selectFile(currFunc)   # strangely enough, this call is not heeded
    filename, fitler_ = saveDialog.getSaveFileName(self, filter = 'Fit function (*.ffunc)', directory=currFunc, caption='Save Fit Function')
    filename = str(filename)
    try:
      savehandle=open(filename,'w')
      # write parameters
      savehandle.write('<PARAMETERS>\n')
      for index, entry in enumerate(self.paramList):
        red = entry + ', ' + self.parent.formatNumber(self.param[index])
        red += ', ' + str(self.param_active[index]) + '\n'
        savehandle.write(red)
      
      # write formula
      savehandle.write('<FORMULA>\n')
      red = str(self.fitFormula.toPlainText())
      savehandle.write(red)
      savehandle.close()
      
      # add function to ffunclist and update selector
      self.ffuncList = self.initFfunc(path=WORKINGDIR + PATH_SEPARATOR + 'functions' + PATH_SEPARATOR)
      self.comboBox.blockSignals(True)
      self.populateFfuncSelector()
      
      # determine index of new function in selector (use short filenames)
      if('/' in filename):
        shortFilename = filename.split('/')[-1]
      elif('\\' in filename):
        shortFilename = filename.split('\\')[-1]
      else:
        shortFilename = filename
        
      index = -1
      for index2, entry in enumerate(self.ffuncList):
        if(shortFilename in entry):
          index = index2

      if(index+1):
        self.comboBox.setCurrentIndex(index)
      else:
        self.comboBox.setCurrentIndex(0)

      self.comboBox.blockSignals(False)
    except:
      self.parent.statusbar.showMessage('Cannot write ' + filename, self.parent.STATUS_TIME)


  def HLine(self):
    # draws a horizontal line
    hline = QtWidgets.QFrame()
    hline.setFrameShape(QtWidgets.QFrame.HLine)
    hline.setFrameShadow(QtWidgets.QFrame.Sunken)
    return hline
  
  def getRelativeDerivatives(self, xval, yval, yerr):
    # determine derivatives of fit parameters
    x, self.startVal = self.parent.fit[self.parent.activeFit].evaluateFunc(x=xval, param=self.param_active_list)
    self.startResid = np.sum((yval - self.startVal)**2 / yerr**2)

    # cycle through parameters and calc. derivatives
    for index, entry in enumerate(self.param_active_list):
      workparam = [i for i in self.param_active_list]
      workparam[index] = self.param[index] * (1.0 + self.EPSILON)
      x, perturbVal = self.parent.fit[self.parent.activeFit].evaluateFunc(x=xval, param=workparam)
      perturbResid = np.sum((yval - perturbVal)**2 / yerr**2)
      # calc. change in chi square when varying a certain parameter
      self.derivatives[index] = (perturbResid - self.startResid)# / self.EPSILON #/ self.EPSILON #startResid

    # now also assign amplitudes for random parameter variation
    self.randomAmplitudes = np.array([1.0/i if i != 0 else 0 for i in self.derivatives])
          
    # calc. relative amplitudes
    divisor = np.max(np.abs(self.randomAmplitudes))
    divisor = np.max((divisor, self.EPSILON))
    self.randomAmplitudes = self.randomAmplitudes / divisor / 2.0

  def doBruteFit(self):
    #import time
    # check whether there is at least one floating parameter
    if(np.sum(self.param_active) == 0):
      self.parent.statusbar.showMessage('At least one parameter has to be free for fitting!', self.parent.STATUS_TIME)
    else:
      # get data from data object and start the fit procedure
      data = self.parent.data[self.parent.activeData].value()
      if((not 'x' in data) or (len(data['x']) < np.sum(self.param_active))):
        try:
          nop = len(data['x'])
        except:
          nop = 0
        self.parent.statusbar.showMessage('No. of data points (' + str(nop) + ') should at least equal no. of free parameters (' + str(np.sum(self.param_active)) + ')!', self.parent.STATUS_TIME)
      elif(('x' in data) and ('y' in data) and (len(data['x']) > 0)):
        # assign values
        xval = np.array(data['x']); yval = np.array(data['y'])
        if('yerr' in data):
          # weed out zero values
          yerr = np.array([i if(i>0) else self.EPSILON for i in data['yerr']])
        else:
          yerr = np.ones(len(data['x']))
          
        # open an extra window to interact with procedure
        self.runFlag = True
        self.daughterWindow = BruteWindow(self, 'Random Search')
        # apply styles to popup window
        if(QSTYLE != None):
          self.daughterWindow.setStyle(QSTYLE)
        if(QSTYLESHEET != None):
          self.daughterWindow.setStyleSheet(QSTYLESHEET)
        self.daughterWindow.show()
        
        # create list of active parameters
        self.param_active_list = [self.param[i] for i, x in enumerate(self.param_active) if (x == 1)]
        self.origParam = [i for i in self.param_active_list]
        
        # cycle until daughter window closed
        movingCursor = '|,/,-,\\'.split(',')
        cursorCount = 0
        lastSuccessLimit = 1e4
        repeatCycleLimit = 5; escalate = [1.8**i for i in range(repeatCycleLimit)]
        residstr = ''
        for repeatCycleCount in range(repeatCycleLimit):
          # update message label
          self.daughterWindow.messageLabel.setText('Repeat cycle ' + str(repeatCycleCount + 1) + '/' + str(repeatCycleLimit))
          
          # parameter derivatives
          self.derivatives = np.zeros(len(self.param_active_list))
          self.getRelativeDerivatives(xval, yval, yerr)
          self.daughterWindow.messageLabel2.setText('resid ' + self.parent.formatNumber(self.startResid) + residstr)
      
          lastSuccessCount = 0
          while ((lastSuccessCount < lastSuccessLimit) and (self.runFlag)):
            # randomly vary parameters
            for trial in range(100):
              lastSuccessCount += 1
              # randomly vary parameters -- add epsilon to get rid of zero parameters
              workamplitude = [i if (np.abs(i) > self.MIN_AMPLITUDE) else (np.sign(i + 1.1 * self.EPSILON) * self.MIN_AMPLITUDE) for i in self.param_active_list]
              workamplitude = escalate[repeatCycleCount] * np.array(workamplitude)
              
              workparam = self.param_active_list  + (workamplitude * (0.33 - np.random.random(len(self.param_active_list))))
              x, perturbVal = self.parent.fit[self.parent.activeFit].evaluateFunc(x=xval, param=workparam)
              perturbResid = np.sum((yval - perturbVal)**2 / yerr**2)
              
              if(perturbResid < self.startResid):
                # improvement, yeah!
                # update params
                self.param_active_list = [i for i in workparam]
                self.updateBruteParam(False)
                # calc. residuals
                self.parent.data[self.parent.activeData].setFval(perturbVal)
                # prepare new round of random search
                self.getRelativeDerivatives(xval, yval, yerr)
                self.daughterWindow.messageLabel2.setText('resid ' + self.parent.formatNumber(self.startResid) + residstr)
                lastSuccessCount = 0
                self.daughterWindow.messageLabel3.setText('Func eval: ' + str(int(np.min((lastSuccessCount,\
                  lastSuccessLimit)))) + '/' + str(int(lastSuccessLimit)))
            
            # periodically update label in daughter window
            cursorCount += 1
            if(cursorCount >= len(movingCursor)):
              cursorCount = 0
            self.daughterWindow.messageLabel3.setText('Func eval: ' + str(int(np.min((lastSuccessCount,\
              lastSuccessLimit)))) + '/' + str(int(lastSuccessLimit)))
            self.daughterWindow.messageLabel4.setText('Working ' + movingCursor[cursorCount])
            # need to still process events
            QtCore.QCoreApplication.processEvents()

          if((repeatCycleCount == 0) or (self.startResid < self.bestResid)):
            # first cycle or improvement
            self.bestParam = [i for i in self.param_active_list]
            self.bestVal = 1.0 * self.startVal
            self.bestResid = 1.0 * self.startResid
            residstr = '; best ' + self.parent.formatNumber(self.bestResid)

          # reset original parameters for next cycle
          self.param_active_list = [i for i in self.origParam]
                      
        # finished all repeat cycles
        self.daughterWindow.close()
        
        # restore best results from previous cycle
        if(repeatCycleCount > 0):
          self.param_active_list = [i for i in self.bestParam]
          self.startVal = 1.0 * self.bestVal
        
        # calc. residuals even if no improvement
        self.parent.data[self.parent.activeData].setFval(self.startVal)
        # after procedure, set new parameters and update curve
        self.updateBruteParam(True)

  def updateBruteParam(self, updateResid=False):
    # update fit parameters once found better resid
    counter = 0
    for index, entry in enumerate(self.param_active):
      if (entry == 1):
        self.param[index] = self.param_active_list[counter]
        counter += 1
    self.parent.fit[self.parent.activeFit].updateParam(self.param_active_list)
    # plot function
    self.parent.fit[self.parent.activeFit].handlePlot = self.parent.plotArea.plotFunction(\
      fitobject = self.parent.fit[self.parent.activeFit], handlePlot = self.parent.fit[self.parent.activeFit].handlePlot)
    # update param table
    self.changeParamTable()
    # also update residuals?
    if(updateResid):
      # generate resid style on the fly
      self.parent.data[self.parent.activeData].Residstyle = copy.deepcopy(self.parent.data[self.parent.activeData].style)
      self.parent.data[self.parent.activeData].ResidLinestyle = copy.deepcopy(self.parent.fit[self.parent.activeFit].style)
      # ensure line is visible to connect dots
      if(self.parent.data[self.parent.activeData].Residstyle['linestyle'] == 'None'):
        self.parent.data[self.parent.activeData].Residstyle['linestyle'] = 'solid'
      # plot residuals
      self.parent.data[self.parent.activeData].handleResid, self.parent.plotArea.handleResidZero = self.parent.plotArea.plotResid(\
        dataobject = self.parent.data[self.parent.activeData], handleResid = self.parent.data[self.parent.activeData].handleResid,\
        handleResidZero = self.parent.plotArea.handleResidZero)
      
  def doGridSearch(self):
    # check whether there is at least one floating parameter
    if(np.sum(self.param_active) == 0):
      self.parent.statusbar.showMessage('At least one parameter has to be free for fitting!', self.parent.STATUS_TIME)
    else:
      # get data from data object and start the fit procedure
      data = self.parent.data[self.parent.activeData].value()
      if((not 'x' in data) or (len(data['x']) < np.sum(self.param_active))):
        try:
          nop = len(data['x'])
        except:
          nop = 0
        self.parent.statusbar.showMessage('No. of data points (' + str(nop) + ') should at least equal no. of free parameters (' + str(np.sum(self.param_active)) + ')!', self.parent.STATUS_TIME)
      elif(('x' in data) and ('y' in data) and (len(data['x']) > 0)):
        # assign values
        xval = np.array(data['x']); yval = np.array(data['y'])
        if('yerr' in data):
          # weed out zero values
          yerr = np.array([i if(i>0) else self.EPSILON for i in data['yerr']])
        else:
          yerr = np.ones(len(data['x']))
          
        # open an extra window to interact with procedure
        self.runFlag = True
        self.daughterWindow = BruteWindow(self, 'Grid Search')
        # apply styles to popup window
        if(QSTYLE != None):
          self.daughterWindow.setStyle(QSTYLE)
        if(QSTYLESHEET != None):
          self.daughterWindow.setStyleSheet(QSTYLESHEET)
        self.daughterWindow.show()
        
        # create list of active parameters
        self.param_active_list = [self.param[i] for i, x in enumerate(self.param_active) if (x == 1)]
        self.origParam = [i for i in self.param_active_list]
        
        # do grid search
        gridParamNum = len(self.origParam)
        maxGridEval = 1e4
        gridStepNum = int(maxGridEval ** (1/gridParamNum)) + 1
        gridSweep = np.log(10)
        gridSteps = np.exp(np.linspace(-gridSweep, gridSweep, int(2.0 * gridStepNum / 3.0) + 1))
        # also search negative values
        gridSteps = np.hstack((gridSteps, -gridSteps[:int(1.0 * gridStepNum / 3.0) + 1]))
        
        # cycle until daughter window closed
        movingCursor = '|,/,-,\\'.split(',')
        updateEvery = 100
        cursorCount = 0
        repeatCycleLimit = 5
        residstr = ''

        # determine starting values
        x, self.startVal = self.parent.fit[self.parent.activeFit].evaluateFunc(x=xval, param=self.origParam)
        self.startResid = np.sum((yval - self.startVal)**2 / yerr**2)

        repeatCycleCount = 0
        while(repeatCycleCount < repeatCycleLimit):
          # update message labels
          self.daughterWindow.messageLabel.setText('Repeat cycle ' + str(repeatCycleCount + 1) + '/' + str(repeatCycleLimit))
          self.daughterWindow.messageLabel2.setText('resid ' + self.parent.formatNumber(self.startResid) + residstr)

          # iteratively advance parameters
          currStep = [0 for i in self.origParam]
          alterParam = 0
          funcEval = 0
          improvement = False
          while((alterParam < gridParamNum) and (self.runFlag)):
            if(currStep[alterParam] < gridStepNum - 2):
              currStep[alterParam] += 1
              currStep[:alterParam] = [0 for i in currStep[:alterParam]]
              alterParam = 0
              
              # assign new parameters
              workparam = [i * gridSteps[j] for i, j in zip(self.origParam, currStep)]
              
              # evaluate function
              x, perturbVal = self.parent.fit[self.parent.activeFit].evaluateFunc(x=xval, param=workparam)
              perturbResid = np.sum((yval - perturbVal)**2 / yerr**2)
              funcEval += 1
              
              # check whether improved
              if(perturbResid < self.startResid):
                # improvement, yeah!
                improvement = True
                # update params
                self.param_active_list = [i for i in workparam]
                self.updateBruteParam(False)
                # calc. residuals
                self.parent.data[self.parent.activeData].setFval(perturbVal)
                # update labels
                self.startResid, self.startVal = perturbResid, perturbVal
                self.daughterWindow.messageLabel2.setText('resid ' + self.parent.formatNumber(self.startResid) + residstr)
                self.daughterWindow.messageLabel3.setText('Func eval: ' + str(int(funcEval)) + '/' + str(int(maxGridEval)))
  
              # periodically update label in daughter window
              if(not(funcEval % updateEvery)):
                cursorCount += 1
                if(cursorCount >= len(movingCursor)):
                  cursorCount = 0
                self.daughterWindow.messageLabel3.setText('Func eval: ' + str(int(funcEval)) + '/' + str(int(maxGridEval)))
                self.daughterWindow.messageLabel4.setText('Working ' + movingCursor[cursorCount])
                # need to still process events
                QtCore.QCoreApplication.processEvents()
            else:
              alterParam += 1

          # finsished this cycle -- update origParam for next cycle
          self.origParam = [i for i in self.param_active_list]
          
          # check whether we had any improvement in this cycle
          if(improvement):
            # advance to next macro cycle
            repeatCycleCount += 1
          else:
            # terminate here
            repeatCycleCount = repeatCycleLimit

        # finished grid search
        self.daughterWindow.close()
        
        # calc. residuals even if no improvement
        self.parent.data[self.parent.activeData].setFval(self.startVal)
        # after procedure, set new parameters and update curve
        self.updateBruteParam(True)

  def doFit(self):
    # check whether there is at least one floating parameter
    if(np.sum(self.param_active) == 0):
      self.parent.statusbar.showMessage('At least one parameter has to be free for fitting!', self.parent.STATUS_TIME)
    else:
      # get data from data object and start the fit procedure
      data = self.parent.data[self.parent.activeData].value()
      # check number of fit parameters vs. data points
      if((not 'x' in data) or (len(data['x']) < np.sum(self.param_active))):
        try:
          nop = len(data['x'])
        except:
          nop = 0
        self.parent.statusbar.showMessage('No. of data points (' + str(nop) + ') should at least equal no. of free parameters (' + str(np.sum(self.param_active)) + ')!', self.parent.STATUS_TIME)
      else:
        success, fitpa, confidence = self.parent.fit[self.parent.activeFit].fitFunc(data)
        if (success):
          # update parameters in list
          counter = 0
          for index, entry in enumerate(self.param_active):
            if (entry):
              self.param[index] = fitpa[counter]
              self.confidence[index] = confidence[counter]
              counter += 1
              
          self.changeParamTable()
          # evaluate fitted function at x values and store in data object
          x, fval = self.parent.fit[self.parent.activeFit].simulateFunc(x = self.parent.data[self.parent.activeData].x)
          self.parent.data[self.parent.activeData].setFval(fval)
          # generate resid style on the fly
          self.parent.data[self.parent.activeData].Residstyle = copy.deepcopy(self.parent.data[self.parent.activeData].style)
          for item in ['linewidth', 'linestyle', 'color']:
            self.parent.data[self.parent.activeData].ResidLinestyle[item] = copy.deepcopy(self.parent.fit[self.parent.activeFit].style[item])
          # ensure line is visible to connect dots
          if(self.parent.data[self.parent.activeData].Residstyle['linestyle'] == 'None'):
            self.parent.data[self.parent.activeData].Residstyle['linestyle'] = 'solid'
          # plot function
          self.parent.fit[self.parent.activeFit].handlePlot = self.parent.plotArea.plotFunction(\
            fitobject = self.parent.fit[self.parent.activeFit], handlePlot = self.parent.fit[self.parent.activeFit].handlePlot)
          # plot residuals
          self.parent.data[self.parent.activeData].handleResid, self.parent.plotArea.handleResidZero = self.parent.plotArea.plotResid(\
            dataobject = self.parent.data[self.parent.activeData], handleResid = self.parent.data[self.parent.activeData].handleResid,\
            handleResidZero = self.parent.plotArea.handleResidZero)
          # and we should update the results table
          new_data, roles = self.parent.data[self.parent.activeData].getData_n_Fit()
          labels = self.parent.data[self.parent.activeData].getLabels()
          self.parent.resultsarea.updateResults(new_data, roles, labels=labels)
          # calculate chi_square
          if('yerr' in data):
            yerr = self.parent.data[self.parent.activeData].yerr
            # weed out zero sigma entries
            zerosigma = yerr[yerr <= 0]
            if(len(zerosigma) > 0):
              self.parent.statusbar.showMessage('Encountered zero/negative sigma values => set to '+str(self.EPSILON), self.parent.STATUS_TIME)
              yerr = np.array([i if(i>0) else self.EPSILON for i in yerr])
          else:
            yerr = np.array([1.0 for i in self.parent.data[self.parent.activeData].x])
          chisquare = self.parent.data[self.parent.activeData].resid**2 / yerr**2
          chisquare = np.sum(chisquare)
          # and we should update the fit information
          nop = np.sum(self.param_active)
          dof = len(self.parent.data[self.parent.activeData].x) - nop
          if(dof > 0):
            red_chisquare = chisquare / dof
          else:
            red_chisquare = 'inf'
          freeparameters = []; fixedparameters = []
          for index, entry in enumerate(self.param_active):
            if(entry):
              freeparameters.append(self.paramList[index] + ' = ' + self.parent.formatNumber(self.param[index])\
                + ' +/- ' + self.parent.formatNumber(self.confidence[index]))
            else:
              fixedparameters.append(self.paramList[index] + ' = ' + self.parent.formatNumber(self.param[index]))
          freestring = '\n'.join(freeparameters)
          fixedstring = '\n'.join(fixedparameters)
          self.outstring = self.fitResultsHeader
          self.outstring += 'degrees of freedom: ' + str(dof) + '\n'
          self.outstring += u'\N{GREEK CAPITAL LETTER CHI}2 ' + self.parent.formatNumber(chisquare) + '\n'
          self.outstring += u'red. \N{GREEK CAPITAL LETTER CHI}2 ' + self.parent.formatNumber(red_chisquare) + '\n\n'
          index = self.comboBox.currentIndex()
          if(index + 1):
            currFunc = self.ffuncList[index]
          else:
            currFunc = ''
          self.outstring += 'function: ' + currFunc + '\n'
          self.outstring += '  ' + '\n  '.join(str(self.fitFormula.toPlainText()).splitlines()) + '\n\n'
          self.outstring += 'free parameters:\n' + freestring + '\n'
          if(len(fixedstring)):
            self.outstring += 'fixed parameters:\n' + fixedstring + '\n'
          self.fitResults.setText(self.outstring)
          self.parent.fit[self.parent.activeFit].fitresults = self.outstring
      
  def changeParamTable(self):
    # fills in values into the parameter table
    for index, entry in enumerate(self.paramList):
      self.ParamTable.cellWidget(index, 1).setText(self.parent.formatNumber(self.param[index]))
      self.ParamTable.cellWidget(index, 2).setText(self.parent.formatNumber(self.confidence[index]))

  def useFit(self, redraw=True):
    # update parameter table
    self.updateParamTable()
    # set fit function
    self.setFfunc(redraw=redraw)

  def setFfunc(self, redraw=True):
    # dynamically assign fit function
    # function body
    ffunc_orig = str(self.fitFormula.toPlainText())
    ffunc = '\t'+'\n\t'.join(ffunc_orig.split('\n'))
    
    ffunc_top = ''; ffunc_header = ''; param_count = 0; fitpa = []
    # cycle over all parameters
    for index, entry in enumerate(self.paramList):
      if(self.param_active[index]):
        param_count += 1
        fitpa.append(float(self.param[index]))
        ffunc_header += ', '+entry
      else:
        ffunc_top += '\t'+entry+' = '+str(float(self.param[index]))+'\n'
    
    ffunc = ffunc_top + ffunc
    
    # update the function in the fit object
    if (self.parent.fit[self.parent.activeFit].updateFunc(ffunc, ffunc_header, testParam=fitpa)):
      # update parameters
      self.parent.fit[self.parent.activeFit].updateParam(fitpa)
      # store this information in current fit function
      if(hasattr(self, 'fitResults')):
        fitresults = self.fitResults.toPlainText()
      else:
        fitresults = ''
      self.parent.fit[self.parent.activeFit].storeInfo(self.paramList, self.param, self.param_active,\
        self.confidence, ffunc_orig, ffunc_header, fitresults)
      # plot function
      self.parent.fit[self.parent.activeFit].handlePlot = self.parent.plotArea.plotFunction(\
        fitobject = self.parent.fit[self.parent.activeFit], handlePlot = self.parent.fit[self.parent.activeFit].handlePlot,\
        redraw=redraw)
      # don't use palettes as these are incompatible with style sheets
      self.fitFormula.setStyleSheet('myQTextEdit {background-color: white;}')
    else:
      # some kind of failure
      if(hasattr(self.parent, 'statusbar')):
        self.parent.statusbar.showMessage('Error setting fit function!', self.parent.STATUS_TIME)
        # don't use palettes as these are incompatible with style sheets
        self.fitFormula.setStyleSheet('myQTextEdit {background-color: rgb(250, 190, 190);}')
   
  def updateParamTable(self):
    # check which params we have
    self.paramList = str(self.declareParamEntry.text()).split(',')
    self.paramList = [i.strip() for i in self.paramList]
    # initialize newly added parameters to 1
    while(len(self.param)<len(self.paramList)):
      self.param.append(1.0)
      self.confidence.append('--')
      self.param_active.append(1)
    # truncate self.param if parameters have been deleted
    if(len(self.param)>len(self.paramList)):
      self.param=self.param[:len(self.paramList)]
      self.confidence=self.confidence[:len(self.paramList)]
      self.param_active=self.param_active[:len(self.paramList)]
    
    # prepare table
    self.ParamTable.setRowCount(len(self.paramList))
    
    # set row height and fix
    self.rowHeight = scaledDPI(BASE_SIZE + 2)
    vheader = self.ParamTable.verticalHeader()
    vheader.setDefaultSectionSize(self.rowHeight)
    vheader.setSectionResizeMode(QtWidgets.QHeaderView.Fixed)
    
    self.chkBoxItem = []
    # set up new param entries
    for index, entry in enumerate(self.paramList):
      self.ParamTable.setVerticalHeaderItem(index, QtWidgets.QTableWidgetItem(entry))

      qchkbox_item = QtWidgets.QCheckBox()
      if(self.param_active[index]):
        qchkbox_item.setChecked(True)
      else:
        qchkbox_item.setChecked(False)
      qchkbox_item.setMinimumSize(QtCore.QSize(scaledDPI(18), scaledDPI(BASE_SIZE)))
      qchkbox_item.setMaximumSize(QtCore.QSize(scaledDPI(18), scaledDPI(BASE_SIZE)))
      qchkbox_item.stateChanged.connect(partial(self.clickParam, index))
      self.ParamTable.setCellWidget(index, 0, qchkbox_item)

      qline_item = QLineEditClick(self.parent.formatNumber(self.param[index]))
      qline_item.setValidator(self.validFloat)
      qline_item.setAlignment(QtCore.Qt.AlignRight)
      qline_item.setMinimumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
      qline_item.setMaximumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
      qline_item.editingFinished.connect(partial(self.editParam, index))
      self.ParamTable.setCellWidget(index, 1, qline_item)

      qlabel_item = QtWidgets.QLabel(self.parent.formatNumber(self.confidence[index]))
      qlabel_item.setMinimumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
      qlabel_item.setMaximumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
      qlabel_item.setAlignment(QtCore.Qt.AlignRight)
      self.ParamTable.setCellWidget(index, 2, qlabel_item)
      
    # set automatic column size
    self.ParamTable.resizeColumnsToContents()
    
  def editParam(self, index):
    try:
      self.param[index] = float(self.ParamTable.cellWidget(index, 1).text())
    except:
      self.param[index] = 0

    # update parameters
    # check whether this parameter is fixed or not
    if (self.param_active[index]):
      fitpa = []
      for index, entry in enumerate(self.param):
        if(self.param_active[index]):
          fitpa.append(entry)
      self.parent.fit[self.parent.activeFit].updateParam(fitpa)
    else:
      # also have to recompile the fit function
      self.setFfunc()

    # plot function
    self.parent.fit[self.parent.activeFit].handlePlot = self.parent.plotArea.plotFunction(\
      fitobject = self.parent.fit[self.parent.activeFit], handlePlot = self.parent.fit[self.parent.activeFit].handlePlot)
    
  def clickParam(self, index):
    # test what state the checkbox now has
    if(self.ParamTable.cellWidget(index, 0).isChecked()):
      self.param_active[index] = 1
    else:
      self.param_active[index] = 0
      self.confidence[index] = '--'
      self.ParamTable.cellWidget(index, 2).setText(str(self.confidence[index]))
    
    # update ffunc and parameters
    fitpa = []
    for index, entry in enumerate(self.param):
      if(self.param_active[index]):
        fitpa.append(entry)
    self.parent.fit[self.parent.activeFit].updateParam(fitpa)
    self.setFfunc()
    # but we should not need to update the plot itself

  def initFfunc(self, path='', pattern='*.ffunc'):
    # returns list of available fit functions
    if(path == ''):
      path = WORKINGDIR + PATH_SEPARATOR + 'functions' + PATH_SEPARATOR
    ffunc_list = glob.glob(path+pattern)
    return ffunc_list
    
  def loadFfunc(self, filename):
    # load fit function
    try:
      # read file contents
      readhandle = open(filename, 'r')
      red = readhandle.readline()
      params = []; formula = ''; mode = 0; values = []; active = []
      while(red):
        if ('<PARAMETERS>' in red):
          mode = 1
        elif ('<FORMULA>' in red):
          mode = 2
        elif (mode == 1):
          red = red.strip()
          if (',' in red):
            temparray = red.split(',')
            params.append(temparray[0])
            try:
              values.append(float(temparray[1]))
            except:
              values.append(0.0)
            if(red.count(',') > 1):
              try:
                active.append(bool(float(temparray[2])))
              except:
                active.append(True)
            else:
              active.append(True)
          else:
            params.append(red)
            values.append(1.0)
            active.append(True)
        elif (mode == 2):
          formula += red
        
        red = readhandle.readline()
        
      readhandle.close()
      success = True
    except:
      success = False; params = []; formula = ''; values = []; active = []
    
    return success, params, formula, values, active
    
  def selectFfunc(self):
    # a new fit function was selected in the list
    index = self.comboBox.currentIndex()
    success, parameters, formula, values, active = self.loadFfunc(self.ffuncList[index])
    if(success):
      self.paramList = parameters
      parameters = ', '.join(parameters)
      self.declareParamEntry.setText(parameters)
      self.fitFormula.setText(formula)
      self.param = values
      self.confidence = ['--']*len(values)
      self.param_active = [1 if i else 0 for i in active]
      self.updateParamTable()
      self.useFit()
    else:
      self.parent.statusbar.showMessage('Cannot load function ' + self.comboBox.currentText() + '!', self.parent.STATUS_TIME)
    
  def restoreFfunc(self, parameters, formula, values, active, fitresults, redraw=True):
    # an existing fit function was restored
    self.paramList = parameters
    parameters = ', '.join(parameters)
    self.declareParamEntry.setText(parameters)
    self.fitFormula.setText(formula)
    self.fitResults.setText(fitresults)
    self.param = values
    self.confidence = ['--']*len(values)
    self.param_active = [1 if i else 0 for i in active]
    self.updateParamTable()
    self.useFit(redraw=redraw)
    
class FitObject(object):
  def __init__(self, parent = None):
    self.parent = parent
    self.parent.zcount += 1
    self.zorder = self.parent.zcount

    # locally import numpy again
    import numpy as np
    # import common functions from numpy for ease of access
    from numpy import abs, arccos, arcsin, arctan, exp, cos, cosh, log, log2, log10, power, sin, sinh, sqrt, tan, tanh
    self.mySpace = locals()
    
    self.param = np.array([])
    self.active = []
    self.paramNames =[]
    self.paramAll = []
    
    # memorize plot formatting
    self.rememberSetting = {}
    # use epsilon as minimum error value
    self.EPSILON = 1e-9
    # initialize handles for graphics
    self.handlePlot = None
    # initialize name
    self.setName('Curve_'+str(len(self.parent.fit)))
    # initialize visibility
    self.visibility = True
    # initialize activity state
    self.retired = False
    # initialize data storage
    self.x = np.array([])
    self.y = np.array([])
    # initalize style
    self.style = {}
    self.style['linewidth'] = 2.0
    self.style['linestyle'] = 'solid'
    self.style['dash_capstyle'] = 'butt'
    #self.style['solid_capstyle'] = 'butt'
    self.style['color'] = [0.89, 0.29, 0.2, 1.0]
    self.style['markerfacecolor'] = [0.89, 0.29, 0.2, 1.0]
    self.style['markerfacecoloralt'] = [0.0, 0.0, 0.0, 1.0]
    self.style['markeredgecolor'] = [0.0, 0.0, 0.0, 1.0]
    self.style['markeredgewidth'] = 1.0
    self.style['markersize'] = 14.0
    self.style['marker'] = 'None'
    self.style['fillstyle'] = 'full'
    
    # initialize funcstr_base
    self.ffuncstr_base = ''
    self.ffunc_header = ''
    self.fitresults = ''
    
    # memorize plot settings
    for key in self.style:
      self.rememberSetting[key] = 'set_' + key + '(' + repr(self.style[key]) + ')'
    
  def reportState(self):
    # reports data content for saveState function
    items = 'name,param,ffuncstr_base,ffunc_header,active,paramNames,confidence,fitresults,paramAll,zorder,retired,x,y'.split(',')
    retv = {}
    
    for entry in items:
      if(hasattr(self, entry)):
        value = self.__dict__[entry]
        if(type(value) == type(np.array([]))):
          value = value.tolist()
        retv[entry] = value
    
    return retv

  def restoreState(self, data={}, zoffset=0):
    # restores data content for loadState function
    for entry in data:
      if(hasattr(self, entry)):
        if(entry in ['x', 'y']):
          value = np.array(data[entry])
        elif(entry == 'zorder'):
          value = data[entry] + zoffset
        elif(entry == 'name'):
          value = data[entry]
          self.setName(value)
        else:
          value = data[entry]
        self.__dict__[entry] = value
        
    # redefine fit function
    if((self.ffuncstr_base != '') or (self.ffunc_header != '')):
      self.updateFunc(self.ffuncstr_base, self.ffunc_header)
      
  def retrieveInfo(self):
    # returns previous fit formula and values etc.
    return self.paramNames, self.ffuncstr_base, self.paramAll, self.active, self.fitresults
    
  def storeInfo(self, paramNames, paramAll, active, confidence, ffuncstr_base, ffunc_header, fitresults):
    self.paramNames = paramNames
    self.paramAll = paramAll
    self.active = active
    self.confidence = confidence
    self.ffuncstr_base = ffuncstr_base
    self.ffunc_header = ffunc_header
    self.fitresults = fitresults

  def setName(self, name='Jane Doe'):
    # updates name of object
    self.name = name
    # update plot if necessary
    if(self.handlePlot != None):
      self.handlePlot.set_label(name)
    self.rememberSetting['name'] = 'set_label(' + repr(self.name) + ')'
    
  def setZOrder(self, zorder=0, redraw=True):
    # updates z order
    self.zorder = zorder
    # update plot if necessary
    if(self.handlePlot != None):
      self.handlePlot.set_zorder(self.zorder + self.parent.zOffset)

      self.rememberSetting['zorder'] = 'set_zorder(' + str(self.zorder + self.parent.zOffset) + ')'
      # update plot
      if(redraw):
        self.parent.plotArea.dataplotwidget.myRefresh()

  def setVisibility(self, state=True, redraw=True):
    # toggles visibility of curve
    self.visibility = state
    if(self.handlePlot != None):
      self.handlePlot.set_visible(state)
      if(self.visibility):
        self.handlePlot.set_label(self.name)
      else:
        self.handlePlot.set_label('_nolegend_')
        
      self.rememberSetting['visibility'] = 'set_visible(' + repr(self.visibility) + ')'
      # update plot
      if(redraw):
        self.parent.plotArea.dataplotwidget.myRefresh()

  def spawned(self, source=None):
    # copies contents of the source object to current object
    # note: we do not need to copy ffunc() since we will redefine it in the new object
    if(source != None):
      copyItems = 'param,style,x,y,visibility,ffuncstr_base,ffunc_header,active,paramNames,confidence,fitresults,paramAll'.split(',') #, ffunc
      for item in copyItems:
        if(hasattr(source, item)):
          sourceItem = copy.deepcopy(getattr(source, item))
          setattr(self, item, sourceItem)
      # redefine fit function
      if((self.ffuncstr_base != '') or (self.ffunc_header != '')):
        self.updateFunc(self.ffuncstr_base, self.ffunc_header)
    
  def drawMe(self, redraw=True):
    # causes curve to be drawn on canvas
    self.handlePlot = self.parent.plotArea.plotFunction(\
      fitobject = self, handlePlot = self.handlePlot, redraw=redraw)
    # set visibility
    if (self.handlePlot != None):
      self.handlePlot.set_visible(self.visibility)

  def getStyle(self):
    # returns the style object
    return self.style
    
  def setStyle(self, key, value, redraw=True):
    # changes the style value
    self.style[key] = value
    # cause plot to be updated
    if(self.handlePlot != None):
      method = 'set_'+key
      if (hasattr(self.handlePlot, method)):
        method2call = getattr(self.handlePlot, method)
        method2call(value)
        self.rememberSetting[key] = 'set_' + key + '(' + repr(value) + ')'
        if(redraw):
          self.parent.plotArea.dataplotwidget.myRefresh()
    
  def updateFunc(self, funcstr_base, ffunc_header, testParam=[]):
    try:
      funcstr = 'def ffunc(self, x' + ffunc_header + '):\n' + funcstr_base + '\n\treturn y'
      # generate ffunc in global namespace (this is needed for Python3 vs. Python2, bummer)
      namespace = self.mySpace
      exec(funcstr, namespace)
      # we need to do some initial test to see whether the function can be called
      if(len(testParam)):
        # determine x-range over which function will be applied => we should test this
        xmin, xmax = self.parent.plotArea.minX, self.parent.plotArea.maxX
        if(self.parent.plotArea.modeX == 'linear'):
          testRange = np.linspace(xmin, xmax, self.parent.plotArea.DATAPOINTS_SIMULATION)
        elif(self.parent.plotArea.modeX == 'log'):
          testRange = np.linspace(np.log(xmin), np.log(xmax), self.parent.plotArea.DATAPOINTS_SIMULATION)
          testRange = np.exp(testRange)
        # call function for test purposes
        retv = namespace['ffunc'](self, testRange, *testParam)
        # check for dimension mismatch
        if(retv.shape != testRange.shape):
          # we found some mismatch b/w x and y -- raise error to prevent program crash
          raise 
      # now define the new function in the object scope
      setattr(FitObject, 'ffunc', namespace['ffunc'])
      self.funcstr_base = funcstr_base
      self.ffunc_header = ffunc_header
      return True
    except:
      return False

  def updateParam(self, param=[]):
    self.param = param
    
  def evaluateFunc(self, x=np.array([]), param=[]):
    # evaluate function for a given param array
    if(len(param) == 0):
      param = self.param
    if(not self.retired):
      # evaluate function
      try:
        retv = self.ffunc(x, *param)
      except:
        # some kind of function problem, return empty array
        # for the future: could do this for each data point individually
        retv = np.array([0 for i in x])

    return x, retv

  def simulateFunc(self, x=np.array([])):
    # is this function still active?
    if(not self.retired):
      # evaluate function
      try:
        retv = self.ffunc(x, *self.param)
      except:
        # some kind of function problem, return empty array
        # for the future: could do this for each data point individually
        retv = np.array([0 for i in x])
        
      # store results for future use
      self.x = x
      self.y = retv
    
    return self.x, self.y
    
  def fitFunc(self, data={}, initpa=[]):
    # check if ffunc is defined
    if (hasattr(FitObject, 'ffunc')):
      if (('x' in data) and ('y' in data)):
        # prepare fit
        maxfev = 100000
        # assign and check y error
        if('yerr' in data):
          sigma = data['yerr']
          sigma = [i if(i>0) else self.EPSILON for i in sigma]
        else:
          sigma = [1]*len(data['y'])
          
        if(not len(initpa)):
          initpa = self.param
          
        # do the actual fit
        try:
          fitpa, covar = optim.curve_fit(self.ffunc, data['x'], data['y'], initpa, sigma, maxfev=maxfev)#, method='lm')
        except:
          # catch all kind of fit problems
          fitpa = initpa
          covar = np.zeros(len(fitpa))
         
        try:
          confidence = np.power(covar.diagonal(), 0.5)
        except:
          # takes care of NaN and similar errors
          confidence = ['--']*len(fitpa)
        
        # check for 'nan' in confidence
        if(type(confidence) == type(np.array([]))):
          nanCheck = np.isnan(confidence)
          nanList = confidence[nanCheck]
          if(nanList.size):
            confidence = ['--']*len(fitpa)

        # update parameters
        self.param = fitpa

        return True, fitpa, confidence
      else:
        return False, [], []
    else:
      self.parent.statusbar.showMessage('No fit function defined!', self.parent.STATUS_TIME)
      return False, [], []

# the extras object is used to draw annotation and text on the canvas
class ExtrasObject(object):
  def __init__(self, parent=None):
    self.parent = parent
    self.parent.zcount += 1
    self.zorder = self.parent.zcount

    self.name = ''
    self.visibility = True
    self.handle = None
    self.extrasType = 'text'
    self.x, self.y = 1, 1
    self.labeltext = 'text'
    self.color = [0.0, 0.0, 0.0, 1.0]
    self.fontsize = 12.0
    self.fontname = 'DejaVu Sans'
    self.rotation = 0.0
    self.horizontalalignment = 'center'
    self.verticalalignment = 'center'
    
    self.arrow__x, self.arrow__y = 2, 2
    self.arrow__arrowstyle = '->'
    self.arrow__head_length, self.arrow__head_width, self.arrow__tail_width = 0.4, 0.4, 0.2
    self.arrow__facecolor, self.arrow__edgecolor = [1.0, 1.0, 1.0, 0.7], [0.0, 0.0, 0.0, 1.0]
    self.arrow__linewidth, self.arrow__linestyle, self.arrow__dash_capstyle = 1.0, 'solid', 'butt'
    self.arrow__shrinkA, self.arrow__shrinkB = 5, 5
    self.arrow__lengthA, self.arrow__lengthB = 0.5, 0.5
    self.arrow__widthA, self.arrow__widthB = 0.5, 0.5
    self.arrow__connector = 'arc3'
    self.arrow__hatch = ''
    
    self.bbox__show = True
    self.bbox__boxstyle = 'square'
    self.bbox__facecolor, self.bbox__edgecolor = [1.0, 1.0, 1.0, 0.7], [0.0, 0.0, 0.0, 1.0]
    self.bbox__linewidth, self.bbox__linestyle, self.bbox__dash_capstyle = 1.0, 'solid', 'butt'
    self.bbox__pad = 0.5
    self.bbox__hatch = ''
    self.bbox__tooth_size, self.bbox__rounding_size = 0.5, 0.5
    
    self.x2, self.y2 = self.arrow__x, self.arrow__y
    self.line__linewidth = 1.0
    self.line__linestyle = 'solid'
    self.line__dash_capstyle = 'butt'
    self.line__color = self.color
    
    # store information for graphics export as Python script
    self.rememberSetting = {}

  def reportState(self):
    # reports data content for saveState function
    items = 'name,zorder,extrasType,x,y,labeltext,color,fontsize,fontname,rotation,horizontalalignment'
    items += ',arrow__x,arrow__y,arrow__facecolor,arrow__edgecolor,arrow__linewidth,arrow__linestyle'
    items += ',arrow__shrinkA,arrow__shrinkB,arrow__arrowstyle,arrow__dash_capstyle,arrow__connector,arrow__hatch'
    items += ',arrow__lengthA,arrow__lengthB,arrow__widthA,arrow__widthB'
    items += ',bbox__show,bbox__boxstyle,bbox__facecolor,bbox__edgecolor'
    items += ',bbox__linewidth,bbox__linestyle,bbox__dash_capstyle,bbox__pad,bbox__hatch,bbox__tooth_size,bbox__rounding_size'
    items += ',x2,y2,line__linewidth,line__linestyle,line__dash_capstyle,line__color'
    items = items.split(',')
    retv = {}
    
    for entry in items:
      if(hasattr(self, entry)):
        value = self.__dict__[entry]
        if(type(value) == type(np.array([]))):
          value = value.tolist()
        retv[entry] = value
    
    return retv

  def restoreState(self, data={}, zoffset=0):
    # restores data content for loadState function
    for entry in data:
      if(hasattr(self, entry)):
        if(entry == 'zorder'):
          value = data[entry] + zoffset
        else:
          value = data[entry]
        self.__dict__[entry] = value

  def drawMe(self, redraw=True):
    # delete previous object if present
    if(self.handle != None):
      self.handle.remove()
      
    # treat lines differently
    if(self.extrasType == 'line'):
      self.handle, = self.parent.plotArea.ax.plot([self.x, self.x2], [self.y, self.y2])
      self.handle.set_marker('None')
      
      # remember settings
      self.rememberSetting['origin'] = 'plot([' + repr(self.x) + ', ' + repr(self.arrow__x) + '], [' 
      self.rememberSetting['origin'] += repr(self.y) + ', ' + repr(self.arrow__y) + '])'
      self.rememberSetting['marker'] = 'set_marker(\'None\')'
      
      # apply styles
      for entry in ['linewidth', 'linestyle', 'color', 'dash_capstyle']:
        if(hasattr(self.handle, 'set_' + entry)):
          method2call = getattr(self.handle, 'set_' + entry)
          method2call(self.__dict__['line__' + entry])
          self.rememberSetting[entry] = 'set_' + entry + '(' + repr(self.__dict__['line__' + entry]) + ')'

      # treat z order separately
      self.handle.set_zorder(self.zorder + self.parent.zOffset)
      self.rememberSetting['zorder'] = 'set_zorder(' + repr(self.zorder + self.parent.zOffset) + ')'

      if(redraw):
        self.parent.plotArea.dataplotwidget.myRefresh()
    else:
      # prepare bbox
      if(self.bbox__show):
        # need to implement pad and rounding_size and tooth_size
        bboxProps = {'boxstyle': self.bbox__boxstyle, 'facecolor': self.bbox__facecolor, 'edgecolor': self.bbox__edgecolor,\
                     'linewidth': self.bbox__linewidth, 'linestyle': self.bbox__linestyle, 'hatch': self.bbox__hatch, 'capstyle': self.bbox__dash_capstyle}
        #bboxProps['pad'] = self.bbox__pad  # this effing will not work under Linux
        bboxProps['boxstyle'] = bboxProps['boxstyle'] + ',pad=' + str(self.bbox__pad)  # this will work under Linux as well
      # causes extras to be drawn on canvas
      if(self.extrasType == 'text'):
        if(self.bbox__show):
          self.handle = self.parent.plotArea.ax.text(self.x, self.y, self.labeltext, bbox=bboxProps)
          # apply bbox properties post creation
          styleObject = self.handle.get_bbox_patch().get_boxstyle()
          boxstyleExtension = ''
          for entry in ['tooth_size', 'rounding_size', 'pad']:
            if(hasattr(styleObject, entry)):
              boxstyleExtension += ',' + entry + '=' + str(self.__dict__['bbox__' + entry])
          bboxProps['boxstyle'] = self.bbox__boxstyle + boxstyleExtension
          self.handle.get_bbox_patch().set_boxstyle(bboxProps['boxstyle'])
          # remember settings
          self.rememberSetting['origin'] = 'text(' + repr(self.x) + ', ' + repr(self.y) + ', ' + repr(self.labeltext)
          self.rememberSetting['origin'] += ', bbox=' + repr(bboxProps) + ')'
        else:
          self.handle = self.parent.plotArea.ax.text(self.x, self.y, self.labeltext)
          self.rememberSetting['origin'] = 'text(' + repr(self.x) + ', ' + repr(self.y) + ', ' + repr(self.labeltext) + ')'
      else:
        # implement check for quadratic connector
        safeConnector = 'arc3'
        if(self.arrow__arrowstyle in ['fancy', 'simple', 'wedge']):
          if(not(self.arrow__connector in ['arc3', 'angle3'])):
            self.parent.statusbar.showMessage('Connector style ' + self.arrow__connector + ' incompatible with ' + self.arrow__arrowstyle + '. Reverting to ' + safeConnector + '!', self.parent.STATUS_TIME)
            self.arrow__connector = safeConnector
  
        # draw annotation (unfortunately, matplotlib hard-codes 'round' capstyle, so this setting won't do anything)
        arrowProps = {'facecolor': self.arrow__facecolor, 'arrowstyle': self.arrow__arrowstyle,\
                      'edgecolor': self.arrow__edgecolor, 'linewidth': self.arrow__linewidth, 'linestyle': self.arrow__linestyle,\
                      'capstyle': self.arrow__dash_capstyle, 'shrinkA': self.arrow__shrinkA, 'shrinkB': self.arrow__shrinkB,\
                      'connectionstyle': self.arrow__connector}#, 'head_length': self.arrow__head_length}
        if(self.bbox__show):
          self.handle = self.parent.plotArea.ax.annotate(self.labeltext, xytext=(self.x, self.y), xy=(self.arrow__x, self.arrow__y), arrowprops=arrowProps, bbox=bboxProps)
          # apply bbox properties post creation
          styleObject = self.handle.get_bbox_patch().get_boxstyle()
          boxstyleExtension = ''
          for entry in ['tooth_size', 'rounding_size', 'pad']:
            if(hasattr(styleObject, entry)):
              boxstyleExtension += ',' + entry + '=' + str(self.__dict__['bbox__' + entry])
          bboxProps['boxstyle'] = self.bbox__boxstyle + boxstyleExtension
          self.handle.get_bbox_patch().set_boxstyle(bboxProps['boxstyle'])
        else:
          self.handle = self.parent.plotArea.ax.annotate(self.labeltext, xytext=(self.x, self.y), xy=(self.arrow__x, self.arrow__y), arrowprops=arrowProps)
        
        # apply properties to annotation
        self.handle.arrow_patch.set_hatch(self.arrow__hatch)
        self.rememberSetting['hatch'] = 'arrow_patch.set_hatch(' + repr(self.arrow__hatch) + ')'
        
        # apply arrow properties post creation
        goodProperties = []
        styleObject = self.handle.arrow_patch.get_arrowstyle()
        self.arrow__head_width, self.arrow__head_length = self.arrow__widthB, self.arrow__lengthB
        self.arrow__tail_width = self.arrow__widthA
        properties = 'arrow__lengthA,arrow__lengthB,arrow__widthA,arrow__widthB,arrow__head_width,arrow__head_length,arrow__tail_width'
        for entry in properties.split(','):
          workArrowStyle = self.arrow__arrowstyle
          currProp = entry.split('__')[-1]
          if(hasattr(styleObject, currProp)):
            workArrowStyle += ', ' + currProp + '=' + str(self.__dict__[entry])
            # try setting this property to thus check wether current style accepts it (this is really ugly but matplotlib wants it like this, grrrrrrrrr)
            try:
              self.handle.arrow_patch.set_arrowstyle(workArrowStyle)
              goodProperties.append(entry)
            except:
              # suck it up and do nothing
              pass
        # check whether any property survived
        if(len(goodProperties)):
          workArrowStyle = self.arrow__arrowstyle
          for entry in goodProperties:
            currProp = entry.split('__')[-1]
            workArrowStyle += ', ' + currProp + '=' + str(self.__dict__[entry])
          # throw in another try for safety's measure
          try:
            self.handle.arrow_patch.set_arrowstyle(workArrowStyle)
          except:
            pass
          # remember this
          self.rememberSetting['arrowstyle'] = 'arrow_patch.set_arrowstyle(' + repr(workArrowStyle) + ')'
        elif('arrowstyle' in self.rememberSetting):
          # delete key from dict
          self.rememberSetting.pop('arrowstyle', None)
          
        # now remember all this
        self.rememberSetting['origin'] = 'annotate(' + repr(self.labeltext) + ', xytext=(' + repr(self.x) + ', ' + repr(self.y) + ')'
        self.rememberSetting['origin'] += ', xy=(' + repr(self.arrow__x) + ', ' + repr(self.arrow__y) + '), arrowprops=' + repr(arrowProps)
        if(self.bbox__show):
          self.rememberSetting['origin'] += ', bbox=' + repr(bboxProps) + ')'
        else:
          self.rememberSetting['origin'] += ')'
  
      # set visibility
      if (self.handle != None):
        self.handle.set_visible(self.visibility)
        self.rememberSetting['visibility'] = 'set_visible(' + repr(self.visibility) + ')'
        
        styleItems = 'color,fontsize,fontname,rotation,horizontalalignment,verticalalignment'.split(',')
        for entry in styleItems:
          if((hasattr(self.handle, 'set_' + entry)) and (hasattr(self, entry))):
            method2call = getattr(self.handle, 'set_' + entry)
            method2call(self.__dict__[entry])
            self.rememberSetting[entry] = 'set_' + entry + '(' + repr(self.__dict__[entry]) + ')'
        
        # treat z order separately
        self.handle.set_zorder(self.zorder + self.parent.zOffset)
        self.rememberSetting['zorder'] = 'set_zorder(' + repr(self.zorder + self.parent.zOffset) + ')'
  
        # process text and check for bad math text
        try:
          self.handle._get_layout(self.parent.plotArea.matplot.canvas.renderer)
        except:
          self.parent.statusbar.showMessage('Problems setting label to ' + self.labeltext + '!', self.parent.STATUS_TIME)
          self.labeltext = self.labeltext.replace('$', '')
        
        self.labeltext = '\n'.join(self.labeltext.split('\\n'))
        self.labeltext = '\t'.join(self.labeltext.split('\\t'))
        self.handle.set_text(self.labeltext)
  
        # need to implement extra check for fontname due to erroneous fonts
        try:
          if(redraw):
            self.parent.plotArea.dataplotwidget.myRefresh()
        except:
          safeFont = 'DejaVu Sans'
          self.parent.statusbar.showMessage('Experiencing problems with font ' + self.fontname + ' -- reverting to ' + safeFont, self.parent.STATUS_TIME)
          self.fontname = safeFont
          self.handle.set_fontname(safeFont)
  
          if(redraw):
            self.parent.plotArea.dataplotwidget.myRefresh()
        
        # adjust remember settings
        self.rememberSetting['text'] = 'set_text(' + repr(self.labeltext) + ')'
        self.rememberSetting['fontname'] = 'set_fontname(' + repr(self.fontname) + ')'

  def setValues(self, valueDict, redraw=True):
    # sets values of the extras object
    tempRedraw = False
    if(type(valueDict) == type({})):
      keys = valueDict.keys()
      for entry in keys:
        if(hasattr(self, entry)):
          if(self.__dict__[entry] != valueDict[entry]):
            tempRedraw = True
          self.__dict__[entry] = valueDict[entry]
          
      if(redraw and tempRedraw):
        self.drawMe(redraw=redraw)
          
  def setVisibility(self, state=True, redraw=True):
    # toggles visibility of extra
    self.visibility = state
    if(self.handle != None):
      self.handle.set_visible(state)
        
      # update plot
      if(redraw):
        self.parent.plotArea.dataplotwidget.myRefresh()

  def spawned(self, source=None):
    # copies contents of the source object to current object
    if(source != None):
      copyItems = 'x,y,visibility,extrasType,labeltext,color,fontsize,fontname,rotation,horizontalalignment'
      copyItems += ',arrow__x,arrow__y,arrow__facecolor,arrow__edgecolor,arrow__linewidth,arrow__linestyle,arrow__dash_capstyle'
      copyItems += ',arrow__shrinkA,arrow__shrinkB,arrow__arrowstyle,arrow__connector,arrow__hatch'
      copyItems += ',arrow__lengthA,arrow__lengthB,arrow__widthA,arrow__widthB'
      copyItems += ',bbox__show,bbox__boxstyle,bbox__facecolor,bbox__edgecolor'
      copyItems += ',bbox__linewidth,bbox__linestyle,bbox__dash_capstyle,bbox__pad,bbox__hatch,bbox__tooth_size,bbox__rounding_size'
      copyItems += ',x2,y2,line__linewidth,line__linestyle,line__dash_capstyle,line__color'
      copyItems = copyItems.split(',')
      for item in copyItems:
        if(hasattr(source, item)):
          sourceItem = copy.deepcopy(getattr(source, item))
          setattr(self, item, sourceItem)
          
  def getStyle(self):
    # returns as dictionary various style settings
    copyItems = 'x,y,visibility,extrasType,labeltext,color,fontsize,fontname,rotation,horizontalalignment'
    copyItems += ',arrow__x,arrow__y,arrow__facecolor,arrow__edgecolor,arrow__linewidth,arrow__linestyle,arrow__dash_capstyle'
    copyItems += ',arrow__shrinkA,arrow__shrinkB,arrow__arrowstyle,arrow__connector,arrow__hatch'
    copyItems += ',arrow__lengthA,arrow__lengthB,arrow__widthA,arrow__widthB'
    copyItems += ',bbox__show,bbox__boxstyle,bbox__facecolor,bbox__edgecolor'
    copyItems += ',bbox__linewidth,bbox__linestyle,bbox__dash_capstyle,bbox__pad,bbox__hatch,bbox__tooth_size,bbox__rounding_size'
    copyItems += ',x2,y2,line__linewidth,line__linestyle,line__dash_capstyle,line__color'
    copyItems = copyItems.split(',')
    style = {}
    for entry in copyItems:
      if(hasattr(self, entry)):
        style[entry] = self.__dict__[entry]
    
    return style
  
  def setStyle(self, key=None, value=0, redraw=True):
    # sets a style setting
    if(hasattr(self, key)):
      if(self.__dict__[key] == value):
        redraw = False
      self.__dict__[key] = value
      if(redraw):
        self.drawMe()

  def setZOrder(self, zorder=0, redraw=True):
    # updates z order
    self.zorder = zorder
    # update plot if necessary
    if(self.handle != None):
      self.handle.set_zorder(self.zorder + self.parent.zOffset)

      # update plot
      if(redraw):
        self.parent.plotArea.dataplotwidget.myRefresh()
    
# the data object holds individual data sets
class DataObject(object):
  def __init__(self, parent=None):
    self.x = np.array([])
    self.y = np.array([])
    self.xerr = np.array([])
    self.yerr = np.array([])
    self.fval = np.array([])
    self.resid = np.array([])
    self.labels = []
    self.parent = parent
    self.parent.zcount += 1
    self.zorder = self.parent.zcount
    self.zorderResid = len(self.parent.data) + 2

    # initalize parameters
    self.initParam()
    
  def initParam(self):    
    # memorize plot formatting
    self.rememberSetting = {}
    self.rememberSettingError = {}
    self.rememberSettingResid = {}
    self.rememberSettingBar = {}
    self.rememberSettingStack = {}
    # initialize handles for graphics
    self.handleData = None
    self.handleErr = None
    self.handleResid = None
    self.handleBar = None
    self.handleStack = None
    # initialize name
    self.setName('Data_' + str(len(self.parent.data)))
    self.setNameResid('Resid_' + str(len(self.parent.data)))
    # initialize visibility
    self.visibility = True
    self.visibilityResid = True
    # initalize style
    self.style = {}
    self.style['linewidth'] = 1.0
    self.style['linestyle'] = 'None'
    self.style['dash_capstyle'] = 'butt'
    #self.style['solid_capstyle'] = 'butt'
    self.style['color'] = [0.89, 0.29, 0.2, 1.0]
    self.style['markerfacecolor'] = [0.89, 0.29, 0.2, 1.0]
    self.style['markerfacecoloralt'] = [0.0, 0.0, 0.0, 1.0]
    self.style['markeredgecolor'] = [0.0, 0.0, 0.0, 1.0]
    self.style['markeredgewidth'] = 1.0
    self.style['markersize'] = 14.0
    self.style['marker'] = 'o'
    self.style['fillstyle'] = 'full'
    
    # intialize error style
    self.Errorstyle = {}
    self.Errorstyle['color'] = [0.89, 0.29, 0.2, 1.0]
    self.Errorstyle['linewidth'] = 1.0
    self.Errorstyle['linestyle'] = 'solid'
    # not supported by matplotlib
    #self.Errorstyle['capstyle'] = 'butt'
    self.Errorstyle['markerfacecolor'] = [0.89, 0.29, 0.2, 1.0]
    self.Errorstyle['markerfacecoloralt'] = [0.0, 0.0, 0.0, 1.0]
    self.Errorstyle['markeredgewidth'] = 1.0
    self.Errorstyle['markersize'] = 14.0
    self.Errorstyle['fillstyle'] = 'full'
    self.Errorstyle['errorInFront'] = False
    self.Errorstyle['visible'] = True
    
    # initialize resid style
    self.Residstyle = copy.deepcopy(self.style)
    self.ResidLinestyle = {}
    self.ResidLinestyle['linewidth'] = 1.0
    self.ResidLinestyle['linestyle'] = 'solid'
    self.ResidLinestyle['dash_capstyle'] = 'butt'
    self.ResidLinestyle['color'] = [0.89, 0.29, 0.2, 1.0]
    
    # initialize bar style
    self.Barstyle = {}
    self.Barstyle['showBar'] = False
    self.Barstyle['linewidth'] = 0.5
    self.Barstyle['linestyle'] = 'solid'
    self.Barstyle['capstyle'] = 'butt'
    self.Barstyle['facecolor'] = [0.8, 0.2, 0.2, 1.0]
    self.Barstyle['edgecolor'] = [0.3, 0.3, 0.3, 1.0]
    self.Barstyle['width'] = 0.1
    self.Barstyle['hatch'] = ''
    self.Barstyle['offset'] = 0
    
    # initialize stack style
    self.Stackstyle = {}
    self.Stackstyle['showStack'] = False
    self.Stackstyle['linewidth'] = 0.5
    self.Stackstyle['linestyle'] = 'solid'
    # not supported by matplotlib
    #self.Stackstyle['capstyle'] = 'butt'
    self.Stackstyle['facecolor'] = [0.2, 0.8, 0.2, 0.5]
    self.Stackstyle['edgecolor'] = [0.3, 0.3, 0.3, 1.0]
    self.Stackstyle['hatch'] = ''
    
    # fine-sort zorder
    self.relativeZOrderError = -0.4
    self.relativeZOrderBar = -0.2

    # memorize plot settings
    for key in self.style:
      self.rememberSetting[key] = 'set_' + key + '(' + repr(self.style[key]) + ')'
    for key in self.Errorstyle:
      if(key != 'errorInFront'):
        self.rememberSettingError[key] = 'set_' + key + '(' + repr(self.Errorstyle[key]) + ')'
    for key in self.Residstyle:
      self.rememberSettingResid[key] = 'set_' + key + '(' + repr(self.Residstyle[key]) + ')'
    for key in self.Barstyle:
      if(not (key in ['showBar', 'offset'])):
        self.rememberSettingBar[key] = 'set_' + key + '(' + repr(self.Barstyle[key]) + ')'
    for key in self.Stackstyle:
      if(key != 'showStack'):
        self.rememberSettingStack[key] = 'set_' + key + '(' + repr(self.Stackstyle[key]) + ')'
    
  def toggleBar(self, showBar):
    # turns on/off bar graphics
    self.Barstyle['showBar'] = showBar
    self.drawMe(rescale=False)

  def toggleStack(self, showStack):
    # turns on/off stack graphics
    self.Stackstyle['showStack'] = showStack
    self.drawMe(rescale=False)

  def reportState(self):
    # reports data content for saveState function
    items = ['name', 'nameResid', 'zorder', 'zorderResid', 'x', 'y', 'xerr', 'yerr', 'fval', 'resid', 'labels']
    retv = {}
    
    for entry in items:
      if(hasattr(self, entry)):
        value = self.__dict__[entry]
        if(type(value) == type(np.array([]))):
          value = value.tolist()
        retv[entry] = value
    
    return retv

  def restoreState(self, data={}, zoffset=0, zoffsetResid=0):
    # restores data content for loadState function
    for entry in data:
      if(hasattr(self, entry)):
        if(entry in ['x', 'y', 'xerr', 'yerr', 'fval', 'resid']):
          value = np.array(data[entry])
        elif(entry in ['zorder']):
          value = data[entry] + zoffset
        elif(entry in ['zorderResid']):
          value = data[entry] + zoffsetResid
        elif(entry == 'name'):
          value = data[entry]
          self.setName(value)
        elif(entry == 'nameResid'):
          value = data[entry]
          self.setNameResid(value)
        else:
          value = data[entry]
        self.__dict__[entry] = value

  def setName(self, name='John Doe'):
    # updates name of object
    self.name = name
    # update plot if necessary
    if(self.handleData != None):
      self.handleData.set_label(self.name)
    self.rememberSetting['name'] = 'set_label(' + repr(self.name) + ')'
    
  def setNameResid(self, name='John Doe'):
    # updates name of object
    self.nameResid = name
    # update plot if necessary
    if(self.handleResid != None):
      self.handleResid.set_label(self.nameResid)
    self.rememberSettingResid['name'] = 'set_label(' + repr(self.nameResid) + ')'
    
  def setZOrderError(self, state=True, redraw=True):
    # toggles relative z order of error bars
    self.Errorstyle['errorInFront'] = state
    if(state):
      self.relativeZOrderError = 0.4
    else:
      self.relativeZOrderError = -0.4
    # reassign z values
    self.setZOrder(self.zorder, redraw=redraw)

  def setZOrderResid(self, zorder=0, redraw=True):
    # updates z order of residuals
    self.zorderResid = zorder
    # update plot if necessary
    if(self.handleResid != None):
      self.handleResid.set_zorder(self.zorderResid + self.parent.zOffset)
      self.rememberSettingResid['zorder'] = 'set_zorder(' + str(self.zorderResid + self.parent.zOffset) + ')'

      if(redraw):
        self.parent.plotArea.dataplotwidget.myRefresh()

  def setZOrder(self, zorder=0, redraw=True):
    # updates z order
    self.zorder = zorder
    # update plot if necessary
    if(self.handleData != None):
      self.handleData.set_zorder(self.zorder + self.parent.zOffset)
      self.rememberSetting['zorder'] = 'set_zorder(' + str(self.zorder + self.parent.zOffset) + ')'
    if(self.handleErr != None):
      self.handleErr[0].set_zorder(self.zorder + self.relativeZOrderError + self.parent.zOffset)
      for entry in self.handleErr[1]:
        entry.set_zorder(self.zorder + self.relativeZOrderError + self.parent.zOffset)
      for entry in self.handleErr[2]:
        entry.set_zorder(self.zorder + self.relativeZOrderError + self.parent.zOffset)
      self.rememberSettingError['zorder'] = 'set_zorder(' + str(self.zorder + self.relativeZOrderError + self.parent.zOffset) + ')'
    if(self.handleBar != None):
      for entry in self.handleBar.patches:
        entry.set_zorder(self.zorder + self.relativeZOrderBar + self.parent.zOffset)
      self.rememberSettingBar['zorder'] = 'set_zorder(' + str(self.zorder + self.relativeZOrderBar + self.parent.zOffset) + ')'
    if(self.handleStack != None):
      self.handleStack.set_zorder(self.zorder + self.relativeZOrderBar + self.parent.zOffset)
      self.rememberSettingStack['zorder'] = 'set_zorder(' + str(self.zorder + self.relativeZOrderBar + self.parent.zOffset) + ')'
      
    # update plot
    if(redraw):
      self.parent.plotArea.dataplotwidget.myRefresh()

  def getData_n_Fit(self):
    # returns data, fit and residuals along with rolestr
    descriptors = ['x', 'xerr', 'y', 'yerr', 'fval', 'resid']
    roles = []
    values = np.array([])
    for entry in descriptors:
      if(len(self.__dict__[entry])):
        if(len(values)):
          values = np.vstack((values, self.__dict__[entry]))
        else:
          values = self.__dict__[entry]
        roles.append(entry)
    
    if(len(values)):
      values = values.transpose()
    return values, roles

  def getLabels(self):
    # returns data labels
    return list(self.labels)

  def setFval(self, fval=np.array([])):
    # updates fitted values and residuals after fit
    if(fval.size):
      self.fval = fval
      self.resid = np.array([i-j for i, j in zip(self.y, self.fval)])

  def setVisibility(self, state=True, redraw=True):
    # toggles visibility of data and error bars
    self.visibility = state
    if(self.handleData != None):
      self.handleData.set_visible(state)
      self.rememberSetting['visibility'] = 'set_visible(' + repr(self.visibility) + ')'
      if(self.visibility):
        self.handleData.set_label(self.name)
      else:
        self.handleData.set_label('_nolegend_')  
    if(self.handleErr != None):
      self.handleErr[0].set_visible(state)
      for entry in self.handleErr[1]:
        entry.set_visible(state)
      for entry in self.handleErr[2]:
        entry.set_visible(state)
      self.rememberSettingError['visibility'] = 'set_visible(' + repr(self.visibility) + ')'
    if(self.handleBar != None):
      for entry in self.handleBar.patches:
        entry.set_visible(state)
      self.rememberSettingBar['visibility'] = 'set_visible(' + repr(self.visibility) + ')'
    if(self.handleStack != None):
      self.handleStack.set_visible(state)
      self.rememberSettingStack['visibility'] = 'set_visible(' + repr(self.visibility) + ')'
      
    # update plot
    if(redraw):
      self.parent.plotArea.dataplotwidget.myRefresh()

  def setVisibilityResid(self, state=True):
    # toggles visibility of residuals
    self.visibilityResid = state
    if(self.handleResid != None):
      self.handleResid.set_visible(state)
      self.rememberSettingResid['visibility'] = 'set_visible(' + repr(self.visibilityResid) + ')'
    # update plot
    self.parent.plotArea.residplotwidget.myRefresh()

  def spawned(self, source=None):
    # copies contents of the source object to current object
    if(source != None):
      copyItems = 'x,y,xerr,yerr,style,Errorstyle,fval,resid,visibility,Residstyle,Barstyle,Stackstyle,visibilityResid,labels,relativeZOrderError,relativeZOrderBar'.split(',')
      for item in copyItems:
        if(hasattr(source, item)):
          sourceItem = copy.deepcopy(getattr(source, item))
          setattr(self, item, sourceItem)
    
  def drawMe(self, redraw=True, rescale=True):
    # causes data to be drawn on canvas
    self.handleData, self.handleErr, self.handleBar, self.handleStack = self.parent.plotArea.plotData(self.value(),\
      dataobject = self, handleData = self.handleData, handleErr = self.handleErr, handleBar=self.handleBar,\
      handleStack=self.handleStack, redraw=False, rescale=rescale)
    # set visibility
    if (self.handleData != None):
      self.handleData.set_visible(self.visibility)
      self.rememberSetting['visibility'] = 'set_visible(' + repr(self.visibility) + ')'
    if (self.handleBar != None):
      for entry in self.handleBar.patches:
        entry.set_visible(self.visibility)
      self.rememberSettingBar['visibility'] = 'set_visible(' + repr(self.visibility) + ')'
    if (self.handleStack != None):
      self.handleStack.set_visible(self.visibility)
      self.rememberSettingStack['visibility'] = 'set_visible(' + repr(self.visibility) + ')'
    # redraw?
    if(redraw):
      self.parent.plotArea.dataplotwidget.myRefresh()

  def drawMeResid(self, redraw=True):
    # causes residuals to be drawn on canvas
    self.handleResid, self.parent.plotArea.handleResidZero = self.parent.plotArea.plotResid(\
      dataobject = self, handleResid = self.handleResid, handleResidZero = self.parent.plotArea.handleResidZero,\
      redraw=redraw)
    # set visibility
    if (self.handleResid != None):
      self.handleResid.set_visible(self.visibilityResid)
      self.rememberSettingResid['visibility'] = 'set_visible(' + repr(self.visibilityResid) + ')'

  def getStyle(self):
    # returns the style object
    return self.style
    
  def getBarStyle(self):
    # returns the barstyle object
    return self.Barstyle
    
  def getStackStyle(self):
    # returns the stackstyle object
    return self.Stackstyle
    
  def getResidStyle(self):
    # returns the residuals style object
    return self.Residstyle
    
  def setResidStyle(self, key, value, redraw=True):
    # changes the style value
    self.Residstyle[key] = value
    # cause plot to be updated
    if(self.handleResid != None):
      method = 'set_'+key
      if (hasattr(self.handleResid, method)):
        method2call = getattr(self.handleResid, method)
        method2call(value)
        self.rememberSettingResid[key] = 'set_' + key + '(' + repr(value) + ')'
        if(redraw):
          self.parent.plotArea.residplotwidget.myRefresh()

  def getResidLineStyle(self):
    # returns the residuals line style object
    return self.ResidLinestyle
    
  def setResidLineStyle(self, key, value, redraw=True):
    # changes the style value
    self.ResidLinestyle[key] = value
    # cause plot to be updated
    if(self.parent.plotArea.handleResidZero != None):
      method = 'set_'+key
      if (hasattr(self.parent.plotArea.handleResidZero, method)):
        method2call = getattr(self.parent.plotArea.handleResidZero, method)
        method2call(value)
        if(redraw):
          self.parent.plotArea.residplotwidget.myRefresh()

  def setStyle(self, key, value, redraw=True):
    # changes the style value
    self.style[key] = value
    # cause plot to be updated
    if(self.handleData != None):
      method = 'set_'+key
      if (hasattr(self.handleData, method)):
        method2call = getattr(self.handleData, method)
        method2call(value)
        self.rememberSetting[key] = 'set_' + key + '(' + repr(value) + ')'
        if(redraw):
          self.parent.plotArea.dataplotwidget.myRefresh()

  def getErrorStyle(self):
    # returns the style object
    return self.Errorstyle
    
  def setErrorStyle(self, key, value, redraw=True):
    # changes the errorstyle value
    self.Errorstyle[key] = value
    # cause plot to be updated
    if(self.handleErr != None):
      if(key in ['errorInFront']):
        self.setZOrderError(state=value, redraw=redraw)
      else:
        method = 'set_'+key
        for entry in self.handleErr[1]:
          # remember the organization of the error handles
          if (hasattr(entry, method)):
            method2call = getattr(entry, method)
            method2call(value)
        for entry in self.handleErr[2]:
          if (hasattr(entry, method)):
            method2call = getattr(entry, method)
            method2call(value)
        self.rememberSettingError[key] = 'set_' + key + '(' + repr(value) + ')'
      # don't connect the error bars by line
      for entry in self.handleErr[1]:
        entry.set_linestyle('None')
      if(redraw):
        self.parent.plotArea.dataplotwidget.myRefresh()

  def setBarStyle(self, key, value, redraw=True):
    # changes the barstyle value
    self.Barstyle[key] = value
    # cause plot to be updated
    if(key in ['showBar', 'offset']):
      self.drawMe(redraw=redraw)
    elif(self.handleBar != None):
      if(key in ['width']):
        # have to trigger redraw to avoid recentering of bars
        self.drawMe(redraw=redraw, rescale=False)
      else:
        method = 'set_'+key
        for entry in self.handleBar.patches:
          if (hasattr(entry, method)):
            method2call = getattr(entry, method)
            method2call(value)
        self.rememberSettingBar[key] = 'set_' + key + '(' + repr(value) + ')'
        if(redraw):
          self.parent.plotArea.dataplotwidget.myRefresh()

  def setStackStyle(self, key, value, redraw=True):
    # changes the stackstyle value
    self.Stackstyle[key] = value
    # cause plot to be updated
    if(key in ['showStack']):
      self.drawMe(redraw=redraw)
    elif(self.handleStack != None):
      method = 'set_'+key
      if (hasattr(self.handleStack, method)):
        method2call = getattr(self.handleStack, method)
        method2call(value)
      self.rememberSettingStack[key] = 'set_' + key + '(' + repr(value) + ')'
      if(redraw):
        self.parent.plotArea.dataplotwidget.myRefresh()

  def setData(self, data=[], roles=[], labels=[]):
    # use this function to change the data value
    # check whether roles have been provided
    if(len(roles)):
      if(('x' in roles) and ('y' in roles)):
        self.x = data[:, roles.index('x')]
        self.y = data[:, roles.index('y')]
        if ('xerr' in roles):
          self.xerr = data[:, roles.index('xerr')]
        else:
          self.xerr = np.array([])
        if ('yerr' in roles):
          self.yerr = data[:, roles.index('yerr')]
        else:
          self.yerr = np.array([])
    else:
      if(len(data)):
        self.xerr = np.array([]); self.yerr = np.array([])
        array_dim = data.shape
        if (len(array_dim)>1 and array_dim[1]>1):
          # okay found valid data, now assign values
          self.x = data[:, 0]
          if (array_dim[1] == 2):
            self.y = data[:, 1]
          elif (array_dim[1] == 3):
            self.y = data[:, 1]
            self.yerr = data[:, 2]
          else:
            self.xerr = data[:, 1]
            self.y = data[:, 2]
            self.yerr = data[:, 3]
    
    # assign labels
    self.labels = labels
            
    # clear fval and resid (need to do this as x values and dimensions probably will have changed)
    self.fval = np.array([])
    self.resid = np.array([])
  
  def value(self):
    # use this function to read out value of data object
    data = {}
    if (len(self.x)):
      data['x'] = self.x
    if (len(self.y)):
      data['y'] = self.y
    if (len(self.xerr)):
      data['xerr'] = self.xerr
    if (len(self.yerr)):
      data['yerr'] = self.yerr
    if (len(self.fval)):
      data['fval'] = self.fval
    if (len(self.resid)):
      data['resid'] = self.resid
      
    return data

class markerStyleMenu(QWidgetMac):
  def __init__(self, parent=None, target=None, residMode=False):
    super(markerStyleMenu, self).__init__(parent)
    self.parent = parent
    self.target = target
    self.residMode = residMode
    
    # float validator
    self.validFloat = QtGui.QDoubleValidator()

    # valid line styles
    self.markerstyles = []
    self.markerstyles.extend(matplotlib.lines.Line2D.markers)
    # weed out duplicate blank items
    blankItems = [i for i in self.markerstyles if i in ['', ' ', 'None', None]]
    while (len(blankItems) - 1):
      killItem = blankItems[-1]
      self.markerstyles = [i for i in self.markerstyles if i != killItem]
      blankItems = blankItems[:-1]
    
    self.fillstyles = [i for i in matplotlib.lines.Line2D.fillStyles if not i in ['', 'none', 'None', None]]
    
    # set up initial values
    if (self.target != None):
      if(self.residMode):
        self.style = self.target.getResidStyle()
      else:
        self.style = self.target.getStyle()
    else:
      self.style = {}
      self.style['markerfacecolor'] = [1.0, 1.0, 1.0, 1.0]
      self.style['markeredgecolor'] = [0.0, 0.0, 0.0, 1.0]
      self.style['markeredgewidth'] = 1.0
      self.style['markersize'] = 8.0
      self.style['marker'] = 'o'
      self.style['fillstyle'] = 'full'
    
    # set up GUI
    self.buildRessource()
    
  def buildRessource(self):
    # build gui
    self.vLayout = QtWidgets.QVBoxLayout(self)
    self.vLayout.setContentsMargins(0, 0, 0, 0)
    self.vLayout.setAlignment(QtCore.Qt.AlignLeft|QtCore.Qt.AlignTop)

    # heading
    self.markerStyleLabel = QtWidgets.QLabel()
    self.markerStyleLabel.setText("<html><head/><body><span style=\"font-size:130%; font-weight:bold;\">Marker</span></body></html>")
    self.vLayout.addWidget(self.markerStyleLabel)    
    
    # marker size
    self.markerSizeGroup = QWidgetMac()
    self.vLayout.addWidget(self.markerSizeGroup)
    self.hLayout = QtWidgets.QHBoxLayout(self.markerSizeGroup)
    self.hLayout.setContentsMargins(0, 0, 0, 0)
    self.hLayout.setAlignment(QtCore.Qt.AlignLeft)
    self.markerSizeLabel = QtWidgets.QLabel('Size')
    self.markerSizeLabel.setMaximumSize(QtCore.QSize(scaledDPI(56), scaledDPI(BASE_SIZE)))
    self.markerSizeLabel.setMinimumSize(QtCore.QSize(scaledDPI(56), scaledDPI(BASE_SIZE)))
    self.hLayout.addWidget(self.markerSizeLabel)
    self.markerSizeEntry = QLineEditClick()
    self.markerSizeEntry.setText(str(self.style['markersize']))
    self.markerSizeEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.markerSizeEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.markerSizeEntry.editingFinished.connect(partial(self.changeStyle, self.target, 'markersize', self.markerSizeEntry, 0.0, 100.0))
    self.markerSizeEntry.setValidator(self.validFloat)
    self.hLayout.addWidget(self.markerSizeEntry)
    
    # marker facecolor
    self.markerFaceColorGroup = QWidgetMac()
    self.vLayout.addWidget(self.markerFaceColorGroup)
    self.hLayout2 = QtWidgets.QHBoxLayout(self.markerFaceColorGroup)
    self.hLayout2.setContentsMargins(0, 0, 0, 0)
    self.hLayout2.setAlignment(QtCore.Qt.AlignLeft)
    self.markerFaceColorLabel = QtWidgets.QLabel('Face')
    self.markerFaceColorLabel.setMaximumSize(QtCore.QSize(scaledDPI(56), scaledDPI(BASE_SIZE)))
    self.markerFaceColorLabel.setMinimumSize(QtCore.QSize(scaledDPI(56), scaledDPI(BASE_SIZE)))
    self.hLayout2.addWidget(self.markerFaceColorLabel)
    
    self.markerFaceColorButton = QPushButtonMac()
    self.markerFaceColorButton.setAutoFillBackground(False)
    colorvalue = [int(i*255.0) for i in self.style['markerfacecolor'][0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.markerFaceColorButton.setStyleSheet(colorstr)
    self.markerFaceColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.markerFaceColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.markerFaceColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.markerFaceColorButton.clicked.connect(partial(self.setColor, target = self.target, key = 'markerfacecolor'))
    self.hLayout2.addWidget(self.markerFaceColorButton)
      
    # marker facecolor
    self.markerEdgeColorLabel = QtWidgets.QLabel('Edge')
    self.markerEdgeColorLabel.setMaximumSize(QtCore.QSize(scaledDPI(34), scaledDPI(BASE_SIZE)))
    self.markerEdgeColorLabel.setMinimumSize(QtCore.QSize(scaledDPI(34), scaledDPI(BASE_SIZE)))
    self.hLayout2.addWidget(self.markerEdgeColorLabel)

    self.markerEdgeColorButton = QPushButtonMac()
    self.markerEdgeColorButton.setAutoFillBackground(False)
    colorvalue = [int(i*255.0) for i in self.style['markeredgecolor'][0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.markerEdgeColorButton.setStyleSheet(colorstr)
    self.markerEdgeColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.markerEdgeColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.markerEdgeColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.markerEdgeColorButton.clicked.connect(partial(self.setColor, target = self.target, key = 'markeredgecolor'))
    self.hLayout2.addWidget(self.markerEdgeColorButton)
      
    # marker edge width
    self.markerEdgeWidthGroup = QWidgetMac()
    self.vLayout.addWidget(self.markerEdgeWidthGroup)
    self.hLayout4 = QtWidgets.QHBoxLayout(self.markerEdgeWidthGroup)
    self.hLayout4.setContentsMargins(0, 0, 0, 0)
    self.hLayout4.setAlignment(QtCore.Qt.AlignLeft)
    self.markerEdgeWidthLabel = QtWidgets.QLabel('Edgewidth')
    self.markerEdgeWidthLabel.setMaximumSize(QtCore.QSize(scaledDPI(56), scaledDPI(BASE_SIZE)))
    self.markerEdgeWidthLabel.setMinimumSize(QtCore.QSize(scaledDPI(56), scaledDPI(BASE_SIZE)))
    self.hLayout4.addWidget(self.markerEdgeWidthLabel)
    self.markerEdgeWidthEntry = QLineEditClick()
    self.markerEdgeWidthEntry.setText(str(self.style['markeredgewidth']))
    self.markerEdgeWidthEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.markerEdgeWidthEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.markerEdgeWidthEntry.editingFinished.connect(partial(self.changeStyle, self.target, 'markeredgewidth', self.markerEdgeWidthEntry, 0.0, 100.0))
    self.markerEdgeWidthEntry.setValidator(self.validFloat)
    self.hLayout4.addWidget(self.markerEdgeWidthEntry)
    
    # marker style
    self.markerStyleGroup = QWidgetMac()
    self.vLayout.addWidget(self.markerStyleGroup)
    self.hLayout5 = QtWidgets.QHBoxLayout(self.markerStyleGroup)
    self.hLayout5.setContentsMargins(0, 0, 0, 0)
    self.hLayout5.setAlignment(QtCore.Qt.AlignLeft)
    self.markerStyleLabel = QtWidgets.QLabel('Style')
    self.markerStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(56), scaledDPI(BASE_SIZE)))
    self.markerStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(56), scaledDPI(BASE_SIZE)))
    self.hLayout5.addWidget(self.markerStyleLabel)
    self.comboStyle = QComboBoxMac()
    for entry in self.markerstyles:
      self.comboStyle.addItem(str(entry))
    if(self.style['marker'] in self.markerstyles):
      currindex = self.markerstyles.index(self.style['marker'])
    else:
      currindex = 0
    self.comboStyle.setCurrentIndex(currindex)
    self.comboStyle.activated.connect(partial(self.selectStyle, self.target, 'marker', self.comboStyle))
    self.comboStyle.setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
    self.comboStyle.setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
    self.hLayout5.addWidget(self.comboStyle)    

    # marker fill style
    self.markerFillStyleGroup = QWidgetMac()
    self.vLayout.addWidget(self.markerFillStyleGroup)
    self.hLayout3 = QtWidgets.QHBoxLayout(self.markerFillStyleGroup)
    self.hLayout3.setContentsMargins(0, 0, 0, 0)
    self.hLayout3.setAlignment(QtCore.Qt.AlignLeft)

    self.markerFillStyleLabel = QtWidgets.QLabel('Fillstyle')
    self.markerFillStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(56), scaledDPI(BASE_SIZE)))
    self.markerFillStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(56), scaledDPI(BASE_SIZE)))
    self.hLayout3.addWidget(self.markerFillStyleLabel)
    self.comboFillStyle = QComboBoxMac()
    for entry in self.fillstyles:
      self.comboFillStyle.addItem(str(entry))
    if(self.style['fillstyle'] in self.fillstyles):
      currindex = self.fillstyles.index(self.style['fillstyle'])
    else:
      currindex = 0
    self.comboFillStyle.setCurrentIndex(currindex)
    self.comboFillStyle.activated.connect(partial(self.selectStyle, self.target, 'fillstyle', self.comboFillStyle))
    self.comboFillStyle.setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
    self.comboFillStyle.setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
    self.hLayout3.addWidget(self.comboFillStyle)    

    self.markerAltColorButton = QPushButtonMac()
    self.markerAltColorButton.setAutoFillBackground(False)
    colorvalue = [int(i*255.0) for i in self.style['markerfacecoloralt'][0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.markerAltColorButton.setStyleSheet(colorstr)
    self.markerAltColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.markerAltColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.markerAltColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.markerAltColorButton.clicked.connect(partial(self.setColor, target = self.target, key = 'markerfacecoloralt'))
    self.hLayout3.addWidget(self.markerAltColorButton)
    
  def setColor(self, target = None, key = None):
    if((target != None) and (key != None)):
      # get current color
      if (key in target.style):
        prevColor = [255*i for i in target.style[key]]
        prevColor = QtGui.QColor(*prevColor)
      else:
        prevColor = QtCore.Qt.black
      # call QColor dialog
      nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
      if (nuColor.isValid()):
        value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
        value = [i/255.0 for i in value]
        if(self.residMode):
          target.setResidStyle(key, value, redraw=True)
        else:
          target.setStyle(key, value, redraw=False)
          # update legend if needed
          self.updateLegend(redraw=True)
    
  def selectStyle(self, target = None, key = None, entryfield = None):
    if((target != None) and (key != None)):
      index = entryfield.currentIndex()
      if(key == 'marker'):
        value = self.markerstyles[index]
      else:
        value = self.fillstyles[index]
      if(key in self.style):
        self.style[key] = value
      if(self.residMode):
        target.setResidStyle(key, value, redraw=True)
      else:
        target.setStyle(key, value, redraw=False)
        # update legend if needed
        self.updateLegend(redraw=True)

  def changeStyle(self, target = None, key = None, entryfield = None, minval = 0, maxval = 1):
    if((target != None) and (key != None)):
      # check paramter boundaries
      try:
        value = float(entryfield.text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        entryfield.setText(str(value))
      if(key in self.style):
        self.style[key] = value
      if(self.residMode):
        target.setResidStyle(key, value, redraw=True)
      else:
        target.setStyle(key, value, redraw=False)
        # update legend if needed
        self.updateLegend(redraw=True)

  def updateLegend(self, redraw=True):
    # does legend need to be updated?
    value = self.parent.parent.parent.plotArea.legendVisible
    if(value or redraw):
      self.parent.parent.parent.plotArea.setLegend(value=value, redraw=redraw)

class lineStyleMenu(QWidgetMac):
  def __init__(self, parent=None, target=None, residMode=False, residZero=False):
    super(lineStyleMenu, self).__init__(parent)
    self.parent = parent
    self.target = target
    self.residMode = residMode
    self.residZero = residZero
    
    # float validator
    self.validFloat = QtGui.QDoubleValidator()

    # valid line styles
    self.linestyles = ['None', '-', '--', '-.', ':']
    self.linestyles = ['None', 'solid', 'dashed', 'dashdot', 'dotted']
    self.dashstyles = ['butt', 'round', 'projecting']
    
    # set up initial values
    if (self.target != None):
      if(self.residMode):
        self.style = self.target.getResidStyle()
      else:
        if(self.residZero):
          self.style = self.parent.parent.parent.data[self.parent.parent.parent.activeData].getResidLineStyle()
        else:
          self.style = self.target.getStyle()
    else:
      self.style = {}
      self.style['linewidth'] = 2.0
      self.style['color'] = [120, 200, 50, 1]
      self.style['linestyle'] = 'solid'
      self.style['dash_capstyle'] = 'butt'
     
    # set up GUI
    self.buildRessource()
    
  def buildRessource(self):
    # build gui
    self.vLayout = QtWidgets.QVBoxLayout(self)
    self.vLayout.setContentsMargins(0, 0, 0, 0)
    self.vLayout.setAlignment(QtCore.Qt.AlignLeft|QtCore.Qt.AlignTop)
    
    # heading
    self.lineStyleLabel = QtWidgets.QLabel()
    self.lineStyleLabel.setText("<html><head/><body><span style=\"font-size:130%; font-weight:bold;\">Line</span></body></html>")
    self.vLayout.addWidget(self.lineStyleLabel)    
    
    # line width
    self.lineWidthGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineWidthGroup)
    self.hLayout = QtWidgets.QHBoxLayout(self.lineWidthGroup)
    self.hLayout.setContentsMargins(0, 0, 0, 0)
    self.hLayout.setAlignment(QtCore.Qt.AlignLeft)
    self.lineWidthLabel = QtWidgets.QLabel('Width')
    self.lineWidthLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.lineWidthLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.hLayout.addWidget(self.lineWidthLabel)
    self.lineWidthEntry = QLineEditClick()
    self.lineWidthEntry.setText(str(self.style['linewidth']))
    self.lineWidthEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.lineWidthEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.lineWidthEntry.editingFinished.connect(partial(self.changeStyle, self.target, 'linewidth', self.lineWidthEntry, 0.0, 100.0))
    self.lineWidthEntry.setValidator(self.validFloat)
    self.hLayout.addWidget(self.lineWidthEntry)
    
    # line color
    self.lineColorGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineColorGroup)
    self.hLayout2 = QtWidgets.QHBoxLayout(self.lineColorGroup)
    self.hLayout2.setContentsMargins(0, 0, 0, 0)
    self.hLayout2.setAlignment(QtCore.Qt.AlignLeft)
    self.lineColorLabel = QtWidgets.QLabel('Color')
    self.lineColorLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.lineColorLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.hLayout2.addWidget(self.lineColorLabel)
      
    self.lineColorButton = QPushButtonMac()
    self.lineColorButton.setAutoFillBackground(False)
    colorvalue = [int(i*255.0) for i in self.style['color'][0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.lineColorButton.setStyleSheet(colorstr)
    self.lineColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.lineColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.lineColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.lineColorButton.clicked.connect(partial(self.setColor, target = self.target, key = 'color'))
    self.hLayout2.addWidget(self.lineColorButton)
      
    # line style
    self.lineStyleGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineStyleGroup)
    self.hLayout3 = QtWidgets.QHBoxLayout(self.lineStyleGroup)
    self.hLayout3.setContentsMargins(0, 0, 0, 0)
    self.hLayout3.setAlignment(QtCore.Qt.AlignLeft)
    self.lineStyleLabel = QtWidgets.QLabel('Style')
    self.lineStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.lineStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.hLayout3.addWidget(self.lineStyleLabel)
    self.comboStyle = QComboBoxMac()
    for entry in self.linestyles:
      self.comboStyle.addItem(entry)
    if(self.style['linestyle'] in self.linestyles):
      currindex = self.linestyles.index(self.style['linestyle'])
    else:
      currindex = 0
    self.comboStyle.setCurrentIndex(currindex)
    self.comboStyle.activated.connect(partial(self.selectStyle, self.target, 'linestyle', self.comboStyle))
    self.comboStyle.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.comboStyle.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.hLayout3.addWidget(self.comboStyle)
    
    # cap style
    self.lineDashStyleGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineDashStyleGroup)
    self.hLayout4 = QtWidgets.QHBoxLayout(self.lineDashStyleGroup)
    self.hLayout4.setContentsMargins(0, 0, 0, 0)
    self.hLayout4.setAlignment(QtCore.Qt.AlignLeft)
    self.lineDashStyleLabel = QtWidgets.QLabel('Cap')
    self.lineDashStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.lineDashStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.hLayout4.addWidget(self.lineDashStyleLabel)
    self.comboDashStyle = QComboBoxMac()
    for entry in self.dashstyles:
      self.comboDashStyle.addItem(entry)
    if(self.style['dash_capstyle'] in self.dashstyles):
      currindex = self.dashstyles.index(self.style['dash_capstyle'])
    else:
      currindex = 0
    self.comboDashStyle.setCurrentIndex(currindex)
    self.comboDashStyle.activated.connect(partial(self.selectStyle, self.target, 'dash_capstyle', self.comboDashStyle))
    self.comboDashStyle.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.comboDashStyle.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.hLayout4.addWidget(self.comboDashStyle)

  def setColor(self, target=None, key=None):
    if((target != None) and (key != None)):
      # get current color
      if (key in self.style):
        prevColor = [255*i for i in self.style[key]]
        prevColor = QtGui.QColor(*prevColor)
      else:
        prevColor = QtCore.Qt.black
      # call QColor dialog
      nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
      if (nuColor.isValid()):
        value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
        value = [i/255.0 for i in value]
        if(self.residMode):
          target.setResidStyle(key, value, redraw=True)
        elif(self.residZero):
          self.parent.parent.parent.data[self.parent.parent.parent.activeData].setResidLineStyle(key, value, redraw=True)
        else:
          target.setStyle(key, value, redraw=False)
          # update legend if needed
          self.updateLegend(redraw=True)
    
  def selectStyle(self, target=None, key=None, entryfield=None):
    if((target != None) and (key != None)):
      value = str(entryfield.currentText())
      if(key in self.style):
        self.style[key] = value
      if(self.residMode):
        target.setResidStyle(key, value, redraw=True)
      elif(self.residZero):
        self.parent.parent.parent.data[self.parent.parent.parent.activeData].setResidLineStyle(key, value, redraw=True)
      else:
        target.setStyle(key, value, redraw=False)
        # update legend if needed
        self.updateLegend(redraw=True)
      
  def changeStyle(self, target=None, key=None, entryfield=None, minval=0, maxval=1):
    if((target != None) and (key != None)):
      # check paramter boundaries
      try:
        value = float(entryfield.text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        entryfield.setText(str(value))
      if(key in self.style):
        self.style[key] = value
      if(self.residMode):
        target.setResidStyle(key, value, redraw=True)
      elif(self.residZero):
        self.parent.parent.parent.data[self.parent.parent.parent.activeData].setResidLineStyle(key, value, redraw=True)
      else:
        target.setStyle(key, value, redraw=False)
        # update legend if needed
        self.updateLegend(redraw=True)

  def updateLegend(self, redraw=True):
    # does legend need to be updated?
    value = self.parent.parent.parent.plotArea.legendVisible
    if(value or redraw):
      self.parent.parent.parent.plotArea.setLegend(value=value, redraw=redraw)

class barStyleMenu(QWidgetMac):
  def __init__(self, parent=None, target=None, residMode=False):
    super(barStyleMenu, self).__init__(parent)
    self.parent = parent
    self.target = target
    self.residMode = residMode
    
    # float validator
    self.validFloat = QtGui.QDoubleValidator()

    # valid line styles
    self.linestyles = ['None', '-', '--', '-.', ':']
    self.linestyles = ['None', 'solid', 'dashed', 'dashdot', 'dotted']
    
    # valid hatch styles
    self.hatchstyles = ['None', '/', '|', '-', '+', 'x', 'o', 'O', '.', '*'] # unfortunately none is not interpreted correctly
    self.hatchstyles = ['', '/', '|', '-', '+', 'x', 'o', 'O', '.', '*']
    self.dashstyles = ['butt', 'round', 'projecting']
    
    # set up initial values
    if (self.target != None):
      self.style = self.target.getBarStyle()
    else:
      self.style = {}
      self.style['linewidth'] = 0.5
      self.style['linestyle'] = 'solid'
      self.style['facecolor'] = [0.8, 0.0, 0.0, 0.5]
      self.style['edgecolor'] = [0.3, 0.3, 0.3, 1.0]
      self.style['width'] = 0.1
      self.style['hatch'] = 'None'
      self.style['showBar'] = False
      self.style['offset'] = 0
    
    # set up GUI
    self.buildRessource()
    
  def buildRessource(self):
    # build gui
    self.vLayout = QtWidgets.QVBoxLayout(self)
    self.vLayout.setContentsMargins(0, 0, 0, 0)
    self.vLayout.setAlignment(QtCore.Qt.AlignLeft|QtCore.Qt.AlignTop)

    # heading
    self.barStyleLabel = QtWidgets.QLabel()
    self.barStyleLabel.setText("<html><head/><body><span style=\"font-size:130%; font-weight:bold;\">Bar</span></body></html>")
    self.vLayout.addWidget(self.barStyleLabel)    
    
    # display bar?
    self.displayGroup = QWidgetMac()
    self.vLayout.addWidget(self.displayGroup)
    self.hLayout0 = QtWidgets.QHBoxLayout(self.displayGroup)
    self.hLayout0.setContentsMargins(0, 0, 0, 0)
    self.hLayout0.setAlignment(QtCore.Qt.AlignLeft)
    self.displayLabel = QtWidgets.QLabel('Show?')
    self.displayLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.displayLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout0.addWidget(self.displayLabel)
    self.displayCheck = QtWidgets.QCheckBox(self.displayGroup)
    self.displayCheck.setGeometry(QtCore.QRect(scaledDPI(2),\
      scaledDPI(2), scaledDPI(18), scaledDPI(18)))
    self.displayCheck.setChecked(self.style['showBar'])
    self.displayCheck.setText('')
    self.displayCheck.stateChanged.connect(partial(self.setDisplay, self.target))
    self.hLayout0.addWidget(self.displayCheck)
    
    # line width
    self.lineWidthGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineWidthGroup)
    self.hLayout = QtWidgets.QHBoxLayout(self.lineWidthGroup)
    self.hLayout.setContentsMargins(0, 0, 0, 0)
    self.hLayout.setAlignment(QtCore.Qt.AlignLeft)
    self.lineWidthLabel = QtWidgets.QLabel('Linewidth')
    self.lineWidthLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.lineWidthLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout.addWidget(self.lineWidthLabel)
    self.lineWidthEntry = QLineEditClick()
    self.lineWidthEntry.setText(str(self.style['linewidth']))
    self.lineWidthEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.lineWidthEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.lineWidthEntry.editingFinished.connect(partial(self.changeStyle, self.target, 'linewidth', self.lineWidthEntry, 0.0, 100.0))
    self.lineWidthEntry.setValidator(self.validFloat)
    self.hLayout.addWidget(self.lineWidthEntry)
    
    # line color
    self.lineColorGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineColorGroup)
    self.hLayout2 = QtWidgets.QHBoxLayout(self.lineColorGroup)
    self.hLayout2.setContentsMargins(0, 0, 0, 0)
    self.hLayout2.setAlignment(QtCore.Qt.AlignLeft)
    self.lineColorLabel = QtWidgets.QLabel('Linecolor')
    self.lineColorLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.lineColorLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout2.addWidget(self.lineColorLabel)
      
    self.lineColorButton = QPushButtonMac()
    self.lineColorButton.setAutoFillBackground(False)
    colorvalue = [int(i*255.0) for i in self.style['edgecolor'][0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.lineColorButton.setStyleSheet(colorstr)
    self.lineColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.lineColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.lineColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.lineColorButton.clicked.connect(partial(self.setColor, target = self.target, key = 'edgecolor'))
    self.hLayout2.addWidget(self.lineColorButton)
      
    # line style
    self.lineStyleGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineStyleGroup)
    self.hLayout3 = QtWidgets.QHBoxLayout(self.lineStyleGroup)
    self.hLayout3.setContentsMargins(0, 0, 0, 0)
    self.hLayout3.setAlignment(QtCore.Qt.AlignLeft)
    self.lineStyleLabel = QtWidgets.QLabel('Linestyle')
    self.lineStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.lineStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout3.addWidget(self.lineStyleLabel)
    self.comboStyle = QComboBoxMac()
    for entry in self.linestyles:
      self.comboStyle.addItem(entry)
    if(self.style['linestyle'] in self.linestyles):
      currindex = self.linestyles.index(self.style['linestyle'])
    else:
      currindex = 0
    self.comboStyle.setCurrentIndex(currindex)
    self.comboStyle.activated.connect(partial(self.selectStyle, self.target, 'linestyle', self.comboStyle))
    self.comboStyle.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.comboStyle.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.hLayout3.addWidget(self.comboStyle)

    # cap style
    self.lineDashStyleGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineDashStyleGroup)
    self.hLayout4 = QtWidgets.QHBoxLayout(self.lineDashStyleGroup)
    self.hLayout4.setContentsMargins(0, 0, 0, 0)
    self.hLayout4.setAlignment(QtCore.Qt.AlignLeft)
    self.lineDashStyleLabel = QtWidgets.QLabel('Linecap')
    self.lineDashStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.lineDashStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout4.addWidget(self.lineDashStyleLabel)
    self.comboDashStyle = QComboBoxMac()
    for entry in self.dashstyles:
      self.comboDashStyle.addItem(entry)
    if(self.style['capstyle'] in self.dashstyles):
      currindex = self.dashstyles.index(self.style['capstyle'])
    else:
      currindex = 0
    self.comboDashStyle.setCurrentIndex(currindex)
    self.comboDashStyle.activated.connect(partial(self.selectStyle, self.target, 'capstyle', self.comboDashStyle))
    self.comboDashStyle.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.comboDashStyle.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.hLayout4.addWidget(self.comboDashStyle)

    # fill color
    self.fillColorGroup = QWidgetMac()
    self.vLayout.addWidget(self.fillColorGroup)
    self.hLayout5 = QtWidgets.QHBoxLayout(self.fillColorGroup)
    self.hLayout5.setContentsMargins(0, 0, 0, 0)
    self.hLayout5.setAlignment(QtCore.Qt.AlignLeft)
    self.fillColorLabel = QtWidgets.QLabel('Fillcolor')
    self.fillColorLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.fillColorLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout5.addWidget(self.fillColorLabel)
      
    self.fillColorButton = QPushButtonMac()
    self.fillColorButton.setAutoFillBackground(False)
    colorvalue = [int(i*255.0) for i in self.style['facecolor'][0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.fillColorButton.setStyleSheet(colorstr)
    self.fillColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.fillColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.fillColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.fillColorButton.clicked.connect(partial(self.setColor, target = self.target, key = 'facecolor'))
    self.hLayout5.addWidget(self.fillColorButton)
      
    # hatch style
    self.hatchStyleGroup = QWidgetMac()
    self.vLayout.addWidget(self.hatchStyleGroup)
    self.hLayout6 = QtWidgets.QHBoxLayout(self.hatchStyleGroup)
    self.hLayout6.setContentsMargins(0, 0, 0, 0)
    self.hLayout6.setAlignment(QtCore.Qt.AlignLeft)
    self.hatchStyleLabel = QtWidgets.QLabel('Hatch')
    self.hatchStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hatchStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout6.addWidget(self.hatchStyleLabel)
    self.comboHatchStyle = QComboBoxMac()
    for entry in self.hatchstyles:
      self.comboHatchStyle.addItem(entry)
    if(self.style['hatch'] in self.hatchstyles):
      currindex = self.hatchstyles.index(self.style['hatch'])
    else:
      currindex = 0
    self.comboHatchStyle.setCurrentIndex(currindex)
    self.comboHatchStyle.activated.connect(partial(self.selectStyle, self.target, 'hatch', self.comboHatchStyle))
    self.comboHatchStyle.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.comboHatchStyle.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.hLayout6.addWidget(self.comboHatchStyle)

    # bar width
    self.barWidthGroup = QWidgetMac()
    self.vLayout.addWidget(self.barWidthGroup)
    self.hLayout7 = QtWidgets.QHBoxLayout(self.barWidthGroup)
    self.hLayout7.setContentsMargins(0, 0, 0, 0)
    self.hLayout7.setAlignment(QtCore.Qt.AlignLeft)
    self.barWidthLabel = QtWidgets.QLabel('Barwidth')
    self.barWidthLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.barWidthLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout7.addWidget(self.barWidthLabel)
    self.barWidthEntry = QLineEditClick()
    self.barWidthEntry.setText(str(self.style['width']))
    self.barWidthEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.barWidthEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.barWidthEntry.editingFinished.connect(partial(self.changeStyle, self.target, 'width', self.barWidthEntry, 0.0, 1000.0))
    self.barWidthEntry.setValidator(self.validFloat)
    self.hLayout7.addWidget(self.barWidthEntry)
    
    # bar offset
    self.barOffsetGroup = QWidgetMac()
    self.vLayout.addWidget(self.barOffsetGroup)
    self.hLayout8 = QtWidgets.QHBoxLayout(self.barOffsetGroup)
    self.hLayout8.setContentsMargins(0, 0, 0, 0)
    self.hLayout8.setAlignment(QtCore.Qt.AlignLeft)
    self.barOffsetLabel = QtWidgets.QLabel('Offset')
    self.barOffsetLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.barOffsetLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout8.addWidget(self.barOffsetLabel)
    self.barOffsetEntry = QLineEditClick()
    self.barOffsetEntry.setText(str(self.style['offset']))
    self.barOffsetEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.barOffsetEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.barOffsetEntry.editingFinished.connect(partial(self.changeStyle, self.target, 'offset', self.barOffsetEntry, -1000.0, 1000.0))
    self.barOffsetEntry.setValidator(self.validFloat)
    self.hLayout8.addWidget(self.barOffsetEntry)
    
  def setDisplay(self, target=None):
    # toggled display of bar graphics
    if(target != None):
      self.style['showBar'] = self.displayCheck.isChecked()
      target.toggleBar(self.style['showBar'])

  def setColor(self, target=None, key=None):
    if((target != None) and (key != None)):
      # get current color
      if (key in self.style):
        prevColor = [255*i for i in self.style[key]]
        prevColor = QtGui.QColor(*prevColor)
      else:
        prevColor = QtCore.Qt.black
      # call QColor dialog
      nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
      if (nuColor.isValid()):
        value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
        value = [i/255.0 for i in value]
        target.setBarStyle(key, value, redraw=True)
        # update legend if needed - not needed as bars do not feature in legend
        #self.updateLegend()
    
  def selectStyle(self, target=None, key=None, entryfield=None):
    if((target != None) and (key != None)):
      #value = str(self.comboStyle.currentText())
      value = str(entryfield.currentText())
      if(key in self.style):
        self.style[key] = value
      target.setBarStyle(key, value, redraw=True)
      # update legend if needed - not needed as bars do not feature in legend
      #self.updateLegend()
      
  def changeStyle(self, target=None, key=None, entryfield=None, minval=0, maxval=1):
    if((target != None) and (key != None)):
      # check paramter boundaries
      try:
        value = float(entryfield.text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        entryfield.setText(str(value))
      if(key in self.style):
        self.style[key] = value
      target.setBarStyle(key, value, redraw=True)
      # update legend if needed - not needed as bars do not feature in legend
      #self.updateLegend()

  def updateLegend(self, redraw=True):
    # does legend need to be updated?
    value = self.parent.parent.parent.plotArea.legendVisible
    if(value or redraw):
      self.parent.parent.parent.plotArea.setLegend(value=value, redraw=redraw)

class stackStyleMenu(QWidgetMac):
  def __init__(self, parent=None, target=None, residMode=False):
    super(stackStyleMenu, self).__init__(parent)
    self.parent = parent
    self.target = target
    self.residMode = residMode
    
    # float validator
    self.validFloat = QtGui.QDoubleValidator()

    # valid line styles
    self.linestyles = ['None', '-', '--', '-.', ':']
    self.linestyles = ['None', 'solid', 'dashed', 'dashdot', 'dotted']
    
    # valid hatch styles
    self.hatchstyles = ['None', '/', '|', '-', '+', 'x', 'o', 'O', '.', '*'] # unfortunately none is not interpreted correctly
    self.hatchstyles = ['', '/', '|', '-', '+', 'x', 'o', 'O', '.', '*']
    self.dashstyles = ['butt', 'round', 'projecting']
    
    # set up initial values
    if (self.target != None):
      self.style = self.target.getStackStyle()
    else:
      self.style = {}
      self.style['linewidth'] = 0.5
      self.style['linestyle'] = 'solid'
      self.style['facecolor'] = [0.8, 0.0, 0.0, 0.5]
      self.style['edgecolor'] = [0.3, 0.3, 0.3, 1.0]
      self.style['hatch'] = 'None'
      self.style['showStack'] = False
    
    # set up GUI
    self.buildRessource()
    
  def buildRessource(self):
    # build gui
    self.vLayout = QtWidgets.QVBoxLayout(self)
    self.vLayout.setContentsMargins(0, 0, 0, 0)
    self.vLayout.setAlignment(QtCore.Qt.AlignLeft|QtCore.Qt.AlignTop)

    # heading
    self.stackStyleLabel = QtWidgets.QLabel()
    self.stackStyleLabel.setText("<html><head/><body><span style=\"font-size:130%; font-weight:bold;\">Stack</span></body></html>")
    self.vLayout.addWidget(self.stackStyleLabel)    
    
    # display stack?
    self.displayGroup = QWidgetMac()
    self.vLayout.addWidget(self.displayGroup)
    self.hLayout0 = QtWidgets.QHBoxLayout(self.displayGroup)
    self.hLayout0.setContentsMargins(0, 0, 0, 0)
    self.hLayout0.setAlignment(QtCore.Qt.AlignLeft)
    self.displayLabel = QtWidgets.QLabel('Show?')
    self.displayLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.displayLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout0.addWidget(self.displayLabel)
    self.displayCheck = QtWidgets.QCheckBox(self.displayGroup)
    self.displayCheck.setGeometry(QtCore.QRect(scaledDPI(2),\
      scaledDPI(2), scaledDPI(18), scaledDPI(18)))
    self.displayCheck.setChecked(self.style['showStack'])
    self.displayCheck.setText('')
    self.displayCheck.stateChanged.connect(partial(self.setDisplay, self.target))
    self.hLayout0.addWidget(self.displayCheck)
    
    # line width
    self.lineWidthGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineWidthGroup)
    self.hLayout = QtWidgets.QHBoxLayout(self.lineWidthGroup)
    self.hLayout.setContentsMargins(0, 0, 0, 0)
    self.hLayout.setAlignment(QtCore.Qt.AlignLeft)
    self.lineWidthLabel = QtWidgets.QLabel('Linewidth')
    self.lineWidthLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.lineWidthLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout.addWidget(self.lineWidthLabel)
    self.lineWidthEntry = QLineEditClick()
    self.lineWidthEntry.setText(str(self.style['linewidth']))
    self.lineWidthEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.lineWidthEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.lineWidthEntry.editingFinished.connect(partial(self.changeStyle, self.target, 'linewidth', self.lineWidthEntry, 0.0, 100.0))
    self.lineWidthEntry.setValidator(self.validFloat)
    self.hLayout.addWidget(self.lineWidthEntry)
    
    # line color
    self.lineColorGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineColorGroup)
    self.hLayout2 = QtWidgets.QHBoxLayout(self.lineColorGroup)
    self.hLayout2.setContentsMargins(0, 0, 0, 0)
    self.hLayout2.setAlignment(QtCore.Qt.AlignLeft)
    self.lineColorLabel = QtWidgets.QLabel('Linecolor')
    self.lineColorLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.lineColorLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout2.addWidget(self.lineColorLabel)
      
    self.lineColorButton = QPushButtonMac()
    self.lineColorButton.setAutoFillBackground(False)
    colorvalue = [int(i*255.0) for i in self.style['edgecolor'][0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.lineColorButton.setStyleSheet(colorstr)
    self.lineColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.lineColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.lineColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.lineColorButton.clicked.connect(partial(self.setColor, target = self.target, key = 'edgecolor'))
    self.hLayout2.addWidget(self.lineColorButton)
      
    # line style
    self.lineStyleGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineStyleGroup)
    self.hLayout3 = QtWidgets.QHBoxLayout(self.lineStyleGroup)
    self.hLayout3.setContentsMargins(0, 0, 0, 0)
    self.hLayout3.setAlignment(QtCore.Qt.AlignLeft)
    self.lineStyleLabel = QtWidgets.QLabel('Linestyle')
    self.lineStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.lineStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout3.addWidget(self.lineStyleLabel)
    self.comboStyle = QComboBoxMac()
    for entry in self.linestyles:
      self.comboStyle.addItem(entry)
    if(self.style['linestyle'] in self.linestyles):
      currindex = self.linestyles.index(self.style['linestyle'])
    else:
      currindex = 0
    self.comboStyle.setCurrentIndex(currindex)
    self.comboStyle.activated.connect(partial(self.selectStyle, self.target, 'linestyle', self.comboStyle))
    self.comboStyle.setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
    self.comboStyle.setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
    self.hLayout3.addWidget(self.comboStyle)

    # cap style => not supported by matplotlib :(
    '''
    self.lineDashStyleGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineDashStyleGroup)
    self.hLayout4 = QtWidgets.QHBoxLayout(self.lineDashStyleGroup)
    self.hLayout4.setContentsMargins(0, 0, 0, 0)
    self.hLayout4.setAlignment(QtCore.Qt.AlignLeft)
    self.lineDashStyleLabel = QtWidgets.QLabel('Linecap')
    self.lineDashStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.lineDashStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout4.addWidget(self.lineDashStyleLabel)
    self.comboDashStyle = QComboBoxMac()
    for entry in self.dashstyles:
      self.comboDashStyle.addItem(entry)
    if(self.style['capstyle'] in self.dashstyles):
      currindex = self.dashstyles.index(self.style['capstyle'])
    else:
      currindex = 0
    self.comboDashStyle.setCurrentIndex(currindex)
    self.comboDashStyle.activated.connect(partial(self.selectStyle, self.target, 'capstyle', self.comboDashStyle))
    self.comboDashStyle.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.comboDashStyle.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.hLayout4.addWidget(self.comboDashStyle)
    '''

    # fill color
    self.fillColorGroup = QWidgetMac()
    self.vLayout.addWidget(self.fillColorGroup)
    self.hLayout5 = QtWidgets.QHBoxLayout(self.fillColorGroup)
    self.hLayout5.setContentsMargins(0, 0, 0, 0)
    self.hLayout5.setAlignment(QtCore.Qt.AlignLeft)
    self.fillColorLabel = QtWidgets.QLabel('Fillcolor')
    self.fillColorLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.fillColorLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout5.addWidget(self.fillColorLabel)
      
    self.fillColorButton = QPushButtonMac()
    self.fillColorButton.setAutoFillBackground(False)
    colorvalue = [int(i*255.0) for i in self.style['facecolor'][0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.fillColorButton.setStyleSheet(colorstr)
    self.fillColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.fillColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.fillColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.fillColorButton.clicked.connect(partial(self.setColor, target = self.target, key = 'facecolor'))
    self.hLayout5.addWidget(self.fillColorButton)
      
    # hatch style
    self.hatchStyleGroup = QWidgetMac()
    self.vLayout.addWidget(self.hatchStyleGroup)
    self.hLayout6 = QtWidgets.QHBoxLayout(self.hatchStyleGroup)
    self.hLayout6.setContentsMargins(0, 0, 0, 0)
    self.hLayout6.setAlignment(QtCore.Qt.AlignLeft)
    self.hatchStyleLabel = QtWidgets.QLabel('Hatch')
    self.hatchStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hatchStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout6.addWidget(self.hatchStyleLabel)
    self.comboHatchStyle = QComboBoxMac()
    for entry in self.hatchstyles:
      self.comboHatchStyle.addItem(entry)
    if(self.style['hatch'] in self.hatchstyles):
      currindex = self.hatchstyles.index(self.style['hatch'])
    else:
      currindex = 0
    self.comboHatchStyle.setCurrentIndex(currindex)
    self.comboHatchStyle.activated.connect(partial(self.selectStyle, self.target, 'hatch', self.comboHatchStyle))
    self.comboHatchStyle.setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
    self.comboHatchStyle.setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
    self.hLayout6.addWidget(self.comboHatchStyle)

  def setDisplay(self, target=None):
    # toggled display of bar graphics
    if(target != None):
      self.style['showStack'] = self.displayCheck.isChecked()
      target.toggleStack(self.style['showStack'])

  def setColor(self, target=None, key=None):
    if((target != None) and (key != None)):
      # get current color
      if (key in self.style):
        prevColor = [255*i for i in self.style[key]]
        prevColor = QtGui.QColor(*prevColor)
      else:
        prevColor = QtCore.Qt.black
      # call QColor dialog
      nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
      if (nuColor.isValid()):
        value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
        value = [i/255.0 for i in value]
        target.setStackStyle(key, value, redraw=True)
        # update legend if needed - not needed as bars do not feature in legend
        #self.updateLegend()
    
  def selectStyle(self, target=None, key=None, entryfield=None):
    if((target != None) and (key != None)):
      #value = str(self.comboStyle.currentText())
      value = str(entryfield.currentText())
      if(key in self.style):
        self.style[key] = value
      target.setStackStyle(key, value, redraw=True)
      # update legend if needed - not needed as bars do not feature in legend
      #self.updateLegend()
      
  def changeStyle(self, target=None, key=None, entryfield=None, minval=0, maxval=1):
    if((target != None) and (key != None)):
      # check paramter boundaries
      try:
        value = float(entryfield.text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        entryfield.setText(str(value))
      if(key in self.style):
        self.style[key] = value
      target.setStackStyle(key, value, redraw=True)
      # update legend if needed - not needed as bars do not feature in legend
      #self.updateLegend()

  def updateLegend(self, redraw=True):
    # does legend need to be updated?
    value = self.parent.parent.parent.plotArea.legendVisible
    if(value or redraw):
      self.parent.parent.parent.plotArea.setLegend(value=value, redraw=redraw)

class errorStyleMenu(QWidgetMac):
  def __init__(self, parent=None, target=None, residMode=False):
    super(errorStyleMenu, self).__init__(parent)
    self.parent = parent
    self.target = target
    self.residMode = residMode

    # float validator
    self.validFloat = QtGui.QDoubleValidator()

    # valid line styles
    self.linestyles = ['None', '-', '--', '-.', ':']
    self.linestyles = ['None', 'solid', 'dashed', 'dashdot', 'dotted']
    self.dashstyles = ['butt', 'round', 'projecting']

    # set up initial values
    if (self.target != None):
      if(self.residMode):
        self.style = self.target.getResidStyle()
      else:
        self.style = self.target.getErrorStyle()
    else:
      self.style = {}
      self.style['color'] = [0.0, 0.0, 0.0, 1.0]
      self.style['linewidth'] = 1.0
      self.style['markeredgewidth'] = 1.0
      self.style['markersize'] = 10.0
      self.style['fillstyle'] = 'full'
      self.style['errorInFront'] = False
    
    # set up GUI
    self.buildRessource()
    
  def buildRessource(self):
    # build gui
    self.vLayout = QtWidgets.QVBoxLayout(self)
    self.vLayout.setContentsMargins(0, 0, 0, 0)
    self.vLayout.setAlignment(QtCore.Qt.AlignLeft|QtCore.Qt.AlignTop)

    # heading
    self.errorStyleLabel = QtWidgets.QLabel()
    self.errorStyleLabel.setText("<html><head/><body><span style=\"font-size:130%; font-weight:bold;\">Error</span></body></html>")
    self.vLayout.addWidget(self.errorStyleLabel)    
    
    # display stack?
    self.displayGroup = QWidgetMac()
    self.vLayout.addWidget(self.displayGroup)
    self.hLayout0 = QtWidgets.QHBoxLayout(self.displayGroup)
    self.hLayout0.setContentsMargins(0, 0, 0, 0)
    self.hLayout0.setAlignment(QtCore.Qt.AlignLeft)
    self.displayLabel = QtWidgets.QLabel('Show?')
    self.displayLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.displayLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout0.addWidget(self.displayLabel)
    self.displayCheck = QtWidgets.QCheckBox(self.displayGroup)
    self.displayCheck.setGeometry(QtCore.QRect(scaledDPI(2),\
      scaledDPI(2), scaledDPI(18), scaledDPI(18)))
    self.displayCheck.setChecked(self.style['visible'])
    self.displayCheck.setText('')
    self.displayCheck.stateChanged.connect(partial(self.setDisplay, self.target))
    self.hLayout0.addWidget(self.displayCheck)

    # line width
    self.lineWidthGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineWidthGroup)
    self.hLayout = QtWidgets.QHBoxLayout(self.lineWidthGroup)
    self.hLayout.setContentsMargins(0, 0, 0, 0)
    self.hLayout.setAlignment(QtCore.Qt.AlignLeft)
    self.lineWidthLabel = QtWidgets.QLabel('Linewidth')
    self.lineWidthLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.lineWidthLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout.addWidget(self.lineWidthLabel)
    self.lineWidthEntry = QLineEditClick()
    self.lineWidthEntry.setText(str(self.style['linewidth']))
    self.lineWidthEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.lineWidthEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.lineWidthEntry.editingFinished.connect(partial(self.changeStyle, self.target, 'linewidth', self.lineWidthEntry, 0.0, 100.0))
    self.lineWidthEntry.setValidator(self.validFloat)
    self.hLayout.addWidget(self.lineWidthEntry)
    
    # line color
    self.lineColorGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineColorGroup)
    self.hLayout2 = QtWidgets.QHBoxLayout(self.lineColorGroup)
    self.hLayout2.setContentsMargins(0, 0, 0, 0)
    self.hLayout2.setAlignment(QtCore.Qt.AlignLeft)
    self.lineColorLabel = QtWidgets.QLabel('Linecolor')
    self.lineColorLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.lineColorLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout2.addWidget(self.lineColorLabel)
    
    self.lineColorButton = QPushButtonMac()
    self.lineColorButton.setAutoFillBackground(False)
    colorvalue = [int(i*255.0) for i in self.style['color'][0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.lineColorButton.setStyleSheet(colorstr)
    self.lineColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.lineColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.lineColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.lineColorButton.clicked.connect(partial(self.setColor, target = self.target, key = 'color'))
    self.hLayout2.addWidget(self.lineColorButton)

    # line style
    self.lineStyleGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineStyleGroup)
    self.hLayout3 = QtWidgets.QHBoxLayout(self.lineStyleGroup)
    self.hLayout3.setContentsMargins(0, 0, 0, 0)
    self.hLayout3.setAlignment(QtCore.Qt.AlignLeft)
    self.lineStyleLabel = QtWidgets.QLabel('Linestyle')
    self.lineStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.lineStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.hLayout3.addWidget(self.lineStyleLabel)
    self.comboStyle = QComboBoxMac()
    for entry in self.linestyles:
      self.comboStyle.addItem(entry)
    if(self.style['linestyle'] in self.linestyles):
      currindex = self.linestyles.index(self.style['linestyle'])
    else:
      currindex = 0
    self.comboStyle.setCurrentIndex(currindex)
    self.comboStyle.activated.connect(partial(self.selectStyle, self.target, 'linestyle', self.comboStyle))
    self.comboStyle.setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
    self.comboStyle.setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
    self.hLayout3.addWidget(self.comboStyle)
    
    # cap style => not supported by matplotlib
    '''
    self.lineDashStyleGroup = QWidgetMac()
    self.vLayout.addWidget(self.lineDashStyleGroup)
    self.hLayout4 = QtWidgets.QHBoxLayout(self.lineDashStyleGroup)
    self.hLayout4.setContentsMargins(0, 0, 0, 0)
    self.hLayout4.setAlignment(QtCore.Qt.AlignLeft)
    self.lineDashStyleLabel = QtWidgets.QLabel('Cap')
    self.lineDashStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.lineDashStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.hLayout4.addWidget(self.lineDashStyleLabel)
    self.comboDashStyle = QComboBoxMac()
    for entry in self.dashstyles:
      self.comboDashStyle.addItem(entry)
    if(self.style['dash_capstyle'] in self.dashstyles):
      currindex = self.dashstyles.index(self.style['dash_capstyle'])
    else:
      currindex = 0
    self.comboDashStyle.setCurrentIndex(currindex)
    self.comboDashStyle.activated.connect(partial(self.selectStyle, self.target, 'dash_capstyle', self.comboDashStyle))
    self.comboDashStyle.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.comboDashStyle.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
    self.hLayout4.addWidget(self.comboDashStyle)
    '''

    # marker edge width
    self.markerEdgeWidthGroup = QWidgetMac()
    self.vLayout.addWidget(self.markerEdgeWidthGroup)
    self.hLayout5 = QtWidgets.QHBoxLayout(self.markerEdgeWidthGroup)
    self.hLayout5.setContentsMargins(0, 0, 0, 0)
    self.hLayout5.setAlignment(QtCore.Qt.AlignLeft)
    self.markerEdgeWidthLabel = QtWidgets.QLabel('Capwidth')
    self.markerEdgeWidthLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.markerEdgeWidthLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout5.addWidget(self.markerEdgeWidthLabel)
    self.markerEdgeWidthEntry = QLineEditClick()
    self.markerEdgeWidthEntry.setText(str(self.style['markeredgewidth']))
    self.markerEdgeWidthEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.markerEdgeWidthEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.markerEdgeWidthEntry.editingFinished.connect(partial(self.changeStyle, self.target, 'markeredgewidth', self.markerEdgeWidthEntry, 0.0, 100.0))
    self.markerEdgeWidthEntry.setValidator(self.validFloat)
    self.hLayout5.addWidget(self.markerEdgeWidthEntry)

    # marker size
    self.markerSizeGroup = QWidgetMac()
    self.vLayout.addWidget(self.markerSizeGroup)
    self.hLayout6 = QtWidgets.QHBoxLayout(self.markerSizeGroup)
    self.hLayout6.setContentsMargins(0, 0, 0, 0)
    self.hLayout6.setAlignment(QtCore.Qt.AlignLeft)
    self.markerSizeLabel = QtWidgets.QLabel('Capsize')
    self.markerSizeLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.markerSizeLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout6.addWidget(self.markerSizeLabel)
    self.markerSizeEntry = QLineEditClick()
    self.markerSizeEntry.setText(str(self.style['markersize']))
    self.markerSizeEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.markerSizeEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.markerSizeEntry.editingFinished.connect(partial(self.changeStyle, self.target, 'markersize', self.markerSizeEntry, 0.0, 100.0))
    self.markerSizeEntry.setValidator(self.validFloat)
    self.hLayout6.addWidget(self.markerSizeEntry)

    # marker size
    self.markerZOrderGroup = QWidgetMac()
    self.vLayout.addWidget(self.markerZOrderGroup)
    self.hLayout7 = QtWidgets.QHBoxLayout(self.markerZOrderGroup)
    self.hLayout7.setContentsMargins(0, 0, 0, 0)
    self.hLayout7.setAlignment(QtCore.Qt.AlignLeft)
    self.markerZOrderLabel = QtWidgets.QLabel('In front?')
    self.markerZOrderLabel.setMaximumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.markerZOrderLabel.setMinimumSize(QtCore.QSize(scaledDPI(52), scaledDPI(BASE_SIZE)))
    self.hLayout7.addWidget(self.markerZOrderLabel)

    self.markerZOrderCheck = QtWidgets.QCheckBox(self.markerZOrderGroup)
    self.markerZOrderCheck.setGeometry(QtCore.QRect(scaledDPI(2),\
      scaledDPI(2), scaledDPI(18), scaledDPI(18)))
    self.markerZOrderCheck.setChecked(self.style['errorInFront'])
    self.markerZOrderCheck.setText('')
    self.markerZOrderCheck.stateChanged.connect(partial(self.setZOrder, self.target))
    self.hLayout7.addWidget(self.markerZOrderCheck)
    
  def setDisplay(self, target=None):
    # toggled display of error bars
    if(target != None):
      self.style['visible'] = self.displayCheck.isChecked()
      target.setErrorStyle('visible', self.style['visible'], redraw=True)

  def setZOrder(self, target=None):
    # toggle relative z order of error bars
    state = self.markerZOrderCheck.isChecked()
    self.style['errorInFront'] = state
    if(target != None):
      target.setZOrderError(state, redraw=True)

  def setColor(self, target=None, key=None):
    if((target != None) and (key != None)):
      # get current color
      if (key in self.style):
        prevColor = [255*i for i in self.style[key]]
        prevColor = QtGui.QColor(*prevColor)
      else:
        prevColor = QtCore.Qt.black
      # call QColor dialog
      nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
      if (nuColor.isValid()):
        value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
        value = [i/255.0 for i in value]
        if(self.residMode):
          target.setResidStyle(key, value, redraw=True)
        else:
          target.setErrorStyle(key, value, redraw=True)
    
  def selectStyle(self, target=None, key=None, entryfield=None):
    if((target != None) and (key != None)):
      value = str(entryfield.currentText())
      if(key in self.style):
        self.style[key] = value
      if(self.residMode):
        target.setResidStyle(key, value, redraw=True)
      else:
        target.setErrorStyle(key, value, redraw=False)
        # update legend if needed
        self.updateLegend(redraw=True)
      
  def changeStyle(self, target=None, key=None, entryfield=None, minval=0, maxval=1):
    if((target != None) and (key != None)):
      # check paramter boundaries
      try:
        value = float(entryfield.text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        entryfield.setText(str(value))
      if(key in self.style):
        self.style[key] = value
      if(self.residMode):
        target.setResidStyle(key, value, redraw=True)
      else:
        target.setErrorStyle(key, value, redraw=True)

  def updateLegend(self, redraw=True):
    # does legend need to be updated?
    value = self.parent.parent.parent.plotArea.legendVisible
    if(value or redraw):
      self.parent.parent.parent.plotArea.setLegend(value=value, redraw=redraw)

class ObjectsArea(QWidgetMac):
  def __init__(self, parent = None):
    super(ObjectsArea, self).__init__()
    self.parent = parent
    
    # set up GUI
    self.buildRessource()
    
  def buildRessource(self):
    # build gui
    self.vLayout = QtWidgets.QVBoxLayout(self)
    self.vLayout.setContentsMargins(0, 0, 0, 0)
    self.dataSetLabel = QtWidgets.QLabel()
    self.dataSetLabel.setText("<html><head/><body><span style=\"font-weight:bold;\">Data sets</span></body></html>")
    self.vLayout.addWidget(self.dataSetLabel)
    self.dataSetTable = QtWidgets.QTableWidget()
    self.vLayout.addWidget(self.dataSetTable)
    self.refreshDataTable()

    self.curvesLabel = QtWidgets.QLabel()
    self.curvesLabel.setText("<html><head/><body><span style=\"font-weight:bold;\">Curves</span></body></html>")
    self.vLayout.addWidget(self.curvesLabel)
    self.curvesTable = QtWidgets.QTableWidget()
    self.vLayout.addWidget(self.curvesTable)
    self.refreshCurvesTable()
    
    self.extrasContainer = QWidgetMac()
    self.hLayout = QtWidgets.QHBoxLayout(self.extrasContainer)
    self.hLayout.setContentsMargins(0, 0, 0, 0)
    self.vLayout.addWidget(self.extrasContainer)
    #
    self.extrasLabel = QtWidgets.QLabel()
    self.extrasLabel.setText("<html><head/><body><span style=\"font-weight:bold;\">Extras</span></body></html>")
    self.hLayout.addWidget(self.extrasLabel)
    self.extrasCreateLineButton = QPushButtonMac()
    self.extrasCreateLineButton.setText('Add Line')
    self.extrasCreateLineButton.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.extrasCreateLineButton.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.extrasCreateLineButton.clicked.connect(partial(self.extrasCreate, 'line'))
    self.hLayout.addWidget(self.extrasCreateLineButton)
    self.extrasCreateTextButton = QPushButtonMac()
    self.extrasCreateTextButton.setText('Add Text')
    self.extrasCreateTextButton.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.extrasCreateTextButton.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.extrasCreateTextButton.clicked.connect(partial(self.extrasCreate, 'text'))
    self.hLayout.addWidget(self.extrasCreateTextButton)
    self.extrasCreateAnnotationButton = QPushButtonMac()
    self.extrasCreateAnnotationButton.setText('Add Annotation')
    self.extrasCreateAnnotationButton.setMinimumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
    self.extrasCreateAnnotationButton.setMaximumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
    self.extrasCreateAnnotationButton.clicked.connect(partial(self.extrasCreate, 'annotation'))
    self.hLayout.addWidget(self.extrasCreateAnnotationButton)

    self.hLayout.addStretch()
    
    self.extrasTable = QtWidgets.QTableWidget()
    self.vLayout.addWidget(self.extrasTable)
    self.refreshExtrasTable()
    
    self.residLabel = QtWidgets.QLabel()
    self.residLabel.setText("<html><head/><body><span style=\"font-weight:bold;\">Residuals</span></body></html>")
    self.vLayout.addWidget(self.residLabel)
    self.residTable = QtWidgets.QTableWidget()
    self.vLayout.addWidget(self.residTable)
    self.refreshResidTable()

  def reportState(self):
    # reports contents for saveState function
    retv = {}
    retv['activeFit'] = self.parent.activeFit
    retv['activeData'] = self.parent.activeData
    
    retstring = ''
    for entry in retv:
      retstring += '>>>' + entry + '\n'
      retstring += repr(retv[entry]) + '\n'
    
    return retstring
  
  def restoreState(self, data, zoffsetData=0, zoffsetCurve=0):
    # restores contents for loadState function
    # fix possible gaps/duplications in zorder
    self.sanityCheckZOrder()
    
    # update tables
    self.refreshDataTable()
    self.refreshResidTable()
    self.refreshCurvesTable()
        
    # set active data set and curve
    if('activeData' in data):
      # check whether new object to be selected exists (can arise from edits in state file)
      if(zoffsetData + data['activeData'] < len(self.parent.data)):
        # turn off previous radio button
        prevActive = self.parent.activeData
        widget = self.dataSetTable.cellWidget(prevActive, 1)
        widget.blockSignals(True)
        widget.setChecked(False)
        widget.blockSignals(False)
        self.residTable.cellWidget(prevActive + 1, 1).setChecked(False)
        
        widget = self.dataSetTable.cellWidget(zoffsetData + data['activeData'], 1)
        widget.setChecked(True)
        self.residTable.cellWidget(zoffsetData + data['activeData'] + 1, 1).setChecked(True)
      
    if('activeFit' in data):
      # check whether new object to be selected exists (can arise from edits in state file)
      if(zoffsetCurve + data['activeFit'] < len(self.parent.fit)):
        # turn off previous radio button
        prevActive = self.parent.activeFit
        widget = self.curvesTable.cellWidget(prevActive, 1)
        widget.blockSignals(True)
        widget.setChecked(False)
        widget.blockSignals(False)
        
        widget = self.curvesTable.cellWidget(zoffsetCurve + data['activeFit'], 1)
        if(widget != None):
          # in case sth. went wrong with the state file
          widget.blockSignals(True)
          widget.setChecked(True)
          widget.blockSignals(False)
          self.changeActiveCurve(zoffsetCurve + data['activeFit'], redraw=False)

  def extrasCreate(self, extrasType='text'):
    # generate extras element
    self.parent.extras.append(ExtrasObject(self.parent))
    if(self.parent.plotArea.modeX == 'linear'):
      x = (self.parent.plotArea.minX + self.parent.plotArea.maxX) / 2.0
      arrow__x = (self.parent.plotArea.minX + 2 * self.parent.plotArea.maxX) / 3.0
    else:
      x = np.exp((np.log(self.parent.plotArea.minX) + np.log(self.parent.plotArea.maxX)) / 2.0)
      arrow__x = np.exp((np.log(self.parent.plotArea.minX) + 2 * np.log(self.parent.plotArea.maxX)) / 3.0)
    if(self.parent.plotArea.modeY == 'linear'):
      y = (self.parent.plotArea.minY + self.parent.plotArea.maxY) / 2.0
      arrow__y = y
    else:
      y = np.exp((np.log(self.parent.plotArea.minY) + np.log(self.parent.plotArea.maxY)) / 2.0)
      arrow__y = y
    x, y, arrow__x, arrow__y = self.roundNumber(x), self.roundNumber(y), self.roundNumber(arrow__x), self.roundNumber(arrow__y)
    x2, y2 = arrow__x, arrow__y
    labeltext = 'Text'
    valueDict = {'x': x, 'y': y, 'labeltext': labeltext, 'extrasType': extrasType,\
                 'arrow__x': arrow__x, 'arrow__y': arrow__y, 'x2': x2, 'y2': y2}
    self.parent.extras[-1].setValues(valueDict, redraw=True)
    
    # update extras table
    self.refreshExtrasTable()
    self.refreshCurvesTable()
    self.refreshDataTable()
      
  def refreshExtrasTable(self):
    # updates extras table
    number_extrasEntry = len(self.parent.extras)
    self.extrasTable.setRowCount(number_extrasEntry)
    self.extrasTable.setColumnCount(6)
    for index, label in enumerate(['vis', 'z', 'text', 'action', '', '']):
      self.extrasTable.setHorizontalHeaderItem(index, QtWidgets.QTableWidgetItem(label))
    # set row height and prevent from resizing
    self.rowHeight = scaledDPI(BASE_SIZE + 2)
    vheader = self.extrasTable.verticalHeader()
    vheader.setDefaultSectionSize(self.rowHeight)

    for index in range(number_extrasEntry):
      vheader.setSectionResizeMode(index, QtWidgets.QHeaderView.Fixed)

      visibilityExtra = QtWidgets.QCheckBox()
      visibilityExtra.setChecked(self.parent.extras[index].visibility)
      visibilityExtra.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE), scaledDPI(BASE_SIZE)))
      visibilityExtra.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE), scaledDPI(BASE_SIZE)))
      visibilityExtra.stateChanged.connect(partial(self.toggleVisibilityExtras, index))
      self.extrasTable.setCellWidget(index, 0, visibilityExtra)
      
      spinselector = QtWidgets.QSpinBox()
      spinselector.setMinimum(1)
      spinselector.setMaximum(self.parent.zcount)
      spinselector.setValue(self.parent.extras[index].zorder)
      spinselector.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      spinselector.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      spinselector.valueChanged.connect(partial(self.changeZOrder, group = 'extras', index = index))
      self.extrasTable.setCellWidget(index, 1, spinselector)

      entryField = QLineEditClick(str(self.parent.extras[index].labeltext))
      entryField.setMinimumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
      entryField.setMaximumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
      entryField.editingFinished.connect(partial(self.editNameExtra, index))
      self.extrasTable.setCellWidget(index, 2, entryField)
      
      extrasButton = QPushButtonMac()
      extrasButton.setText('Conf')
      extrasButton.setMinimumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      extrasButton.setMaximumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      extrasButton.clicked.connect(partial(self.changeStyleExtra, index))
      self.extrasTable.setCellWidget(index, 3, extrasButton)

      extrasButton = QPushButtonMac()
      extrasButton.setText('Copy')
      extrasButton.setMinimumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      extrasButton.setMaximumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      extrasButton.clicked.connect(partial(self.copyExtra, index))
      self.extrasTable.setCellWidget(index, 4, extrasButton)
        
      extrasButton = QPushButtonMac()
      extrasButton.setText('Del')
      extrasButton.setMinimumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      extrasButton.setMaximumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      extrasButton.clicked.connect(partial(self.deleteExtra, index))
      self.extrasTable.setCellWidget(index, 5, extrasButton)
    
    # resize columns
    self.extrasTable.resizeColumnsToContents()

  def sanityCheckZOrder(self):    
    # checks for inconsistencies in zorder (can happen upon restoration/deletion of entries)
    # refresh tables is probably necessary but should be done outside this function
    # data sets and curves
    zorders = {}
    for entry in self.parent.data:
      key = entry.zorder
      while(key in zorders):
        key += 0.001
      zorders[key] = entry
    for entry in self.parent.fit:
      key = entry.zorder
      while(key in zorders):
        key += 0.001
      zorders[key] = entry
    for entry in self.parent.extras:
      key = entry.zorder
      while(key in zorders):
        key += 0.001
      zorders[key] = entry
    
    # reassign zorder values
    keys = sorted(list(zorders.keys()))
    index = 1
    for entry in keys:
      zorders[entry].setZOrder(index, redraw=False)
      index +=1
      
    # residuals
    zordersResid = {}
    # populate with resid zero line
    zordersResid[self.parent.plotArea.zorderResidLine] = 'zero_line'
    for entry in self.parent.data:
      key = entry.zorderResid
      while(key in zordersResid):
        key += 0.001
      zordersResid[key] = entry
    
    # reassign zorderResid values
    keys = sorted(list(zordersResid.keys()))
    index = 1
    for entry in keys:
      if(zordersResid[entry] == 'zero_line'):
        self.parent.plotArea.setZOrderResidLine(index, redraw=False)
      else:
        zordersResid[entry].setZOrderResid(index, redraw=False)
      index +=1
      
  def refreshResidTable(self):
    # updates resid table
    number_residEntry = len(self.parent.data)
    self.residTable.setRowCount(number_residEntry+1)
    self.residTable.setColumnCount(5)
    #self.residTable.horizontalHeader().hide()
    for index, label in enumerate(['vis', 'act', 'z', 'name', 'action']):
      self.residTable.setHorizontalHeaderItem(index, QtWidgets.QTableWidgetItem(label))
    # set row height and prevent from resizing
    self.rowHeight = scaledDPI(BASE_SIZE + 2)
    vheader = self.residTable.verticalHeader()
    vheader.setDefaultSectionSize(self.rowHeight)
    # set up group box for active curve selection
    self.activeResidBox = QtWidgets.QGroupBox()

    for index in range(number_residEntry+1):
      vheader.setSectionResizeMode(index, QtWidgets.QHeaderView.Fixed)

      visibilityResid = QtWidgets.QCheckBox()
      if(index):
        visibilityResid.setChecked(self.parent.data[index-1].visibilityResid)
      else:
        visibilityResid.setChecked(self.parent.plotArea.visibilityResidLine)
      visibilityResid.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE), scaledDPI(BASE_SIZE)))
      visibilityResid.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE), scaledDPI(BASE_SIZE)))
      visibilityResid.stateChanged.connect(partial(self.toggleVisibilityResid, index))
      self.residTable.setCellWidget(index, 0, visibilityResid)

      if(index):
        radiobutton = QtWidgets.QRadioButton(self.activeResidBox)
        radiobutton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE), scaledDPI(BASE_SIZE)))
        radiobutton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE), scaledDPI(BASE_SIZE)))
        radiobutton.setChecked(index-1 == self.parent.activeData)
        radiobutton.setText('')
        radiobutton.setEnabled(False)
        self.residTable.setCellWidget(index, 1, radiobutton)

      spinselector = QtWidgets.QSpinBox()
      spinselector.setMinimum(1)
      spinselector.setMaximum(len(self.parent.data)+1)
      if(index):
        spinselector.setValue(self.parent.data[index-1].zorderResid)
      else:
        spinselector.setValue(self.parent.plotArea.zorderResidLine)
      spinselector.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      spinselector.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      spinselector.valueChanged.connect(partial(self.changeZOrderResid, index = index))
      self.residTable.setCellWidget(index, 2, spinselector)

      if(index):
        entryField = QLineEditClick(str(self.parent.data[index-1].nameResid))
        entryField.editingFinished.connect(partial(self.editNameResid, self.parent.data[index-1], index))
      else:
        entryField = QLineEditClick('zero line')
      entryField.setMinimumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
      entryField.setMaximumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
      self.residTable.setCellWidget(index, 3, entryField)
      
      residButton = QPushButtonMac()
      residButton.setText('Conf')
      residButton.setMinimumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      residButton.setMaximumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      if(index):
        residButton.clicked.connect(partial(self.changeStyle, self.parent.data[index-1], False, True))
      else:
        residButton.clicked.connect(self.changeResidZeroStyle)
      self.residTable.setCellWidget(index, 4, residButton)
        
    # resize columns
    self.residTable.resizeColumnsToContents()

  def refreshCurvesTable(self):
    # updates curves table
    number_curveEntry = len(self.parent.fit)
    self.curvesTable.setRowCount(number_curveEntry)
    self.curvesTable.setColumnCount(7)
    for index, label in enumerate(['vis', 'act', 'z', 'name', 'action', '', '']):
      self.curvesTable.setHorizontalHeaderItem(index, QtWidgets.QTableWidgetItem(label))
    # set row height and prevent from resizing
    self.rowHeight = scaledDPI(BASE_SIZE + 2)
    vheader = self.curvesTable.verticalHeader()
    vheader.setDefaultSectionSize(self.rowHeight)
    # set up group box for active curve selection
    self.activeCurveBox = QtWidgets.QGroupBox()

    for index in range(number_curveEntry):
      vheader.setSectionResizeMode(index, QtWidgets.QHeaderView.Fixed)

      visibilityCurve = QtWidgets.QCheckBox()
      visibilityCurve.setChecked(self.parent.fit[index].visibility)
      visibilityCurve.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE), scaledDPI(BASE_SIZE)))
      visibilityCurve.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE), scaledDPI(BASE_SIZE)))
      visibilityCurve.stateChanged.connect(partial(self.toggleVisibilityCurve, index))
      self.curvesTable.setCellWidget(index, 0, visibilityCurve)
      
      radiobutton = QtWidgets.QRadioButton(self.activeCurveBox)
      radiobutton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE), scaledDPI(BASE_SIZE)))
      radiobutton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE), scaledDPI(BASE_SIZE)))
      radiobutton.setChecked(index == self.parent.activeFit)
      radiobutton.toggled.connect(partial(self.changeActiveCurve, index))
      radiobutton.setText('')
      self.curvesTable.setCellWidget(index, 1, radiobutton)

      spinselector = QtWidgets.QSpinBox()
      spinselector.setMinimum(1)
      spinselector.setMaximum(self.parent.zcount)
      spinselector.setValue(self.parent.fit[index].zorder)
      spinselector.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      spinselector.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      spinselector.valueChanged.connect(partial(self.changeZOrder, group = 'curve', index = index))
      self.curvesTable.setCellWidget(index, 2, spinselector)

      entryField = QLineEditClick(str(self.parent.fit[index].name))
      entryField.setMinimumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
      entryField.setMaximumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
      entryField.editingFinished.connect(partial(self.editNameCurve, self.parent.fit[index], index))
      self.curvesTable.setCellWidget(index, 3, entryField)
      
      curveButton = QPushButtonMac()
      curveButton.setText('Conf')
      curveButton.setMinimumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      curveButton.setMaximumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      curveButton.clicked.connect(partial(self.changeStyle, self.parent.fit[index], False))
      self.curvesTable.setCellWidget(index, 4, curveButton)

      curveButton = QPushButtonMac()
      curveButton.setText('Copy')
      curveButton.setMinimumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      curveButton.setMaximumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      curveButton.clicked.connect(partial(self.copyFit, index))
      self.curvesTable.setCellWidget(index, 5, curveButton)
        
      curveButton = QPushButtonMac()
      curveButton.setText('Del')
      curveButton.setMinimumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      curveButton.setMaximumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      curveButton.clicked.connect(partial(self.deleteCurve, index, True))
      self.curvesTable.setCellWidget(index, 6, curveButton)
    
    # resize columns
    self.curvesTable.resizeColumnsToContents()

  def refreshDataTable(self):
    # updates data table
    number_dataEntry = len(self.parent.data)
    self.dataSetTable.setRowCount(number_dataEntry)
    self.dataSetTable.setColumnCount(7)
    for index, label in enumerate(['vis', 'act', 'z', 'name', 'action', '', '']):
      self.dataSetTable.setHorizontalHeaderItem(index, QtWidgets.QTableWidgetItem(label))
    # set row height and prevent from resizing
    self.rowHeight = scaledDPI(BASE_SIZE + 2)
    vheader = self.dataSetTable.verticalHeader()
    vheader.setDefaultSectionSize(self.rowHeight)
    # set up group box for active curve selection
    self.activeDataSetBox = QtWidgets.QGroupBox()

    for index in range(number_dataEntry):
      vheader.setSectionResizeMode(index, QtWidgets.QHeaderView.Fixed)

      visibilityData = QtWidgets.QCheckBox()
      visibilityData.setChecked(self.parent.data[index].visibility)
      visibilityData.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE), scaledDPI(BASE_SIZE)))
      visibilityData.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE), scaledDPI(BASE_SIZE)))
      visibilityData.stateChanged.connect(partial(self.toggleVisibilityData, index))
      self.dataSetTable.setCellWidget(index, 0, visibilityData)

      radiobutton = QtWidgets.QRadioButton(self.activeDataSetBox)
      radiobutton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE), scaledDPI(BASE_SIZE)))
      radiobutton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE), scaledDPI(BASE_SIZE)))
      radiobutton.setChecked(index == self.parent.activeData)
      radiobutton.toggled.connect(partial(self.changeActiveDataSet, index))
      radiobutton.setText('')
      self.dataSetTable.setCellWidget(index, 1, radiobutton)

      spinselector = QtWidgets.QSpinBox()
      spinselector.setMinimum(1)
      spinselector.setMaximum(self.parent.zcount)
      spinselector.setValue(self.parent.data[index].zorder)
      spinselector.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      spinselector.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      spinselector.valueChanged.connect(partial(self.changeZOrder, group = 'data', index = index))
      self.dataSetTable.setCellWidget(index, 2, spinselector)

      entryField = QLineEditClick(str(self.parent.data[index].name))
      entryField.setMinimumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
      entryField.setMaximumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
      entryField.editingFinished.connect(partial(self.editNameData, self.parent.data[index], index))
      self.dataSetTable.setCellWidget(index, 3, entryField)

      dataButton = QPushButtonMac()
      dataButton.setText('Conf')
      dataButton.setMinimumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      dataButton.setMaximumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      dataButton.clicked.connect(partial(self.changeStyle, self.parent.data[index], True))
      self.dataSetTable.setCellWidget(index, 4, dataButton)

      dataButton = QPushButtonMac()
      dataButton.setText('Copy')
      dataButton.setMinimumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      dataButton.setMaximumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      dataButton.clicked.connect(partial(self.copyData, index))
      self.dataSetTable.setCellWidget(index, 5, dataButton)
        
      dataButton = QPushButtonMac()
      dataButton.setText('Del')
      dataButton.setMinimumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      dataButton.setMaximumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      dataButton.clicked.connect(partial(self.deleteDataSet, index))
      self.dataSetTable.setCellWidget(index, 6, dataButton)
    
    # resize columns
    self.dataSetTable.resizeColumnsToContents()

  def deleteExtra(self, index, redraw=True):
    # deletes extra
    killObject = self.parent.extras[index]
    
    # delete from plot
    killObject.handle.remove()

    # delete from self.parent.fit
    nuList = [self.parent.extras[i] for i in range(len(self.parent.extras)) if (i != index)]
    self.parent.extras = nuList

    # destroy object
    del killObject
    
    # adjust zorders etc.
    self.parent.zcount -= 1
    self.sanityCheckZOrder()
    self.refreshDataTable()
    self.refreshCurvesTable()
    self.refreshExtrasTable()

    # update legend
    self.parent.plotArea.dataplotwidget.myRefresh()

  def deleteCurve(self, index, redraw=True):
    # deletes curve
    if(len(self.parent.fit) == 1):
      self.parent.statusbar.showMessage('Cannot delete last and only curve!', self.parent.STATUS_TIME)
    else:
      killObject = self.parent.fit[index]
      
      # delete from plot
      killObject.handlePlot.remove()

      # delete from self.parent.fit
      nuList = [self.parent.fit[i] for i in range(len(self.parent.fit)) if (i != index)]
      self.parent.fit = nuList

      if(index == self.parent.activeFit):
        # our active fit was deleted, too bad
        if(self.parent.activeFit):
          self.parent.activeFit -= 1
        # activate new function
        self.parent.fit[self.parent.activeFit].retired = False
        # change fit formula
        parameters, formula, values, active, fitresults = self.parent.fit[self.parent.activeFit].retrieveInfo()
        self.parent.fitarea.restoreFfunc(parameters, formula, values, active, fitresults, redraw=False)
      elif((index < self.parent.activeFit) and (self.parent.activeFit > 0)):
        # need to shift number of activeFit
        self.parent.activeFit -= 1
      
      # destroy object
      del killObject
      
      # adjust zorders etc.
      self.parent.zcount -= 1
      self.sanityCheckZOrder()
      self.refreshDataTable()
      self.refreshCurvesTable()
      self.refreshExtrasTable()

      # update legend
      self.updateLegend(redraw=redraw)

  def deleteDataSet(self, index, redraw=True):
    # deletes data set
    if(len(self.parent.data) == 1):
      self.parent.statusbar.showMessage('Cannot delete last and only data set!', self.parent.STATUS_TIME)
    else:
      killObject = self.parent.data[index]
      
      # delete from plot
      items = 'handleData,handleErr,handleResid,handleBar,handleStack'.split(',')
      for entry in items:
        if(killObject.__dict__[entry] != None):
          if(entry != 'handleErr'):
            killObject.__dict__[entry].remove()
          else:
            killObject.__dict__[entry][0].remove()
            for entry2 in killObject.__dict__[entry][1]:
              entry2.remove()
            for entry2 in killObject.__dict__[entry][2]:
              entry2.remove()

      # delete from self.parent.data
      nuList = [self.parent.data[i] for i in range(len(self.parent.data)) if (i != index)]
      self.parent.data = nuList

      if(index == self.parent.activeData):
        # our active data set was deleted, too bad
        if(self.parent.activeData):
          self.parent.activeData -= 1
          # update results table to active data set
          values, descriptors = self.parent.data[self.parent.activeData].getData_n_Fit()
          labels = self.parent.data[self.parent.activeData].getLabels()
          self.parent.resultsarea.updateResults(values, descriptors, labels=labels)
      elif((index < self.parent.activeData) and (self.parent.activeData > 0)):
        # need to shift number of activeFit
        self.parent.activeData -= 1
      
      # destroy object
      del killObject
      
      # adjust zorders etc.
      self.parent.zcount -= 1
      self.sanityCheckZOrder()
      self.refreshDataTable()
      self.refreshCurvesTable()
      self.refreshResidTable()
      self.refreshExtrasTable()

      # update legend
      self.updateLegend(redraw=redraw)
      if(redraw):
        self.parent.plotArea.residplotwidget.myRefresh()

  def changeActiveCurve(self, index=0, redraw=True):
    # changes active curve 
    if(len(self.parent.fit) - 1):
      prevActive = self.parent.activeFit
      if(prevActive != index):
        # update active fit function
        self.parent.activeFit = index
        # stuff to do
        # 1. retire previous function
        self.parent.fit[prevActive].retired = True
        #self.parent.fit[prevActive].retireMe()
        # 2. activate new function
        self.parent.fit[self.parent.activeFit].retired = False
        # change fit formula
        parameters, formula, values, active, fitresults = self.parent.fit[self.parent.activeFit].retrieveInfo()
        self.parent.fitarea.restoreFfunc(parameters, formula, values, active, fitresults, redraw=redraw)
        # change fit parameter table
        # change last fit results
    else:
      # have to set button to checked to prevent turning off
      widget = self.curvesTable.cellWidget(0, 1)
      widget.blockSignals(True)
      widget.setChecked(True)
      widget.blockSignals(False)
  
  def changeActiveDataSet(self, index=0, setCheck=True):
    # changes active data set
    if(len(self.parent.data) - 1):
      prevActive = self.parent.activeData
      if(prevActive != index):
        # update active data set and residuals
        self.parent.activeData = index
        if(setCheck):
          self.residTable.cellWidget(index + 1, 1).setChecked(True)
        # update results table to active data set
        values, descriptors = self.parent.data[self.parent.activeData].getData_n_Fit()
        labels = self.parent.data[self.parent.activeData].getLabels()
        self.parent.resultsarea.updateResults(values, descriptors, labels=labels)
    else:
      # have to set button to checked to prevent turning off
      widget = self.dataSetTable.cellWidget(0, 1)
      widget.blockSignals(True)
      widget.setChecked(True)
      widget.blockSignals(False)
  
  def changeZOrderResid(self, index=0):
    # updates z-order of plot items
    source_index = index
    new_zorder = self.residTable.cellWidget(index, 2).value()
    if(source_index):
      sourceItem = self.parent.data[source_index-1]
      orig_zorder = sourceItem.zorderResid
    else:
      sourceItem = self.parent.plotArea
      orig_zorder = sourceItem.zorderResidLine

    # hunt for the item that needs to be swapped in z-order
    flag = False
    # parse data sets
    for index in range(len(self.parent.data) + 1):
      if(index == 0):
        if(self.parent.plotArea.zorderResidLine == new_zorder):
          target_index = index
          flag = True
      elif(self.parent.data[index-1].zorderResid == new_zorder):
        # we found the guy
        target_index = index
        flag = True

    # now swap the z-order values
    if (flag):
      dest_qspin = self.residTable.cellWidget(target_index, 2)
      # have to temporarily disable event logging
      dest_qspin.blockSignals(True)
      dest_qspin.setValue(orig_zorder)
      dest_qspin.blockSignals(False)
      # update z-order in source object
      if(source_index):
        sourceItem.setZOrderResid(new_zorder, redraw=False)
      else:
        sourceItem.setZOrderResidLine(new_zorder, redraw=False)
      # update z-order in destination object
      if(target_index):
        self.parent.data[target_index-1].setZOrderResid(orig_zorder, redraw=False)
      else:
        self.parent.plotArea.setZOrderResidLine(orig_zorder, redraw=False)

      # trigger redrawing of objects
      self.parent.plotArea.residplotwidget.myRefresh()

  def changeZOrder(self, group='data', index=0):
    # updates z-order of plot items
    if(group in ['data', 'curve', 'extras']):
      # determine field that triggered event
      if (group == 'data'):
        sourceItem = self.parent.data[index]
        new_zorder = self.dataSetTable.cellWidget(index, 2).value()
      elif(group == 'curve'):
        sourceItem = self.parent.fit[index]
        new_zorder = self.curvesTable.cellWidget(index, 2).value()
      else:
        sourceItem = self.parent.extras[index]
        new_zorder = self.extrasTable.cellWidget(index, 1).value()
      orig_zorder = sourceItem.zorder
      
      # hunt for the item that needs to be swapped in z-order
      flag = False
      # parse data sets
      for index in range(len(self.parent.data)):
        if(self.parent.data[index].zorder == new_zorder):
          # we found the guy
          flag = True
          dest_qspin = self.dataSetTable.cellWidget(index, 2)
          # have to temporarily disable event logging
          dest_qspin.blockSignals(True)
          dest_qspin.setValue(orig_zorder)
          dest_qspin.blockSignals(False)
          destItem = self.parent.data[index]
          index = len(self.parent.data)+1
      # parse curves
      if (not flag):
        for index in range(len(self.parent.fit)):
          if(self.parent.fit[index].zorder == new_zorder):
            # we found the guy
            flag = True
            dest_qspin = self.curvesTable.cellWidget(index, 2)
            # have to temporarily disable event logging
            dest_qspin.blockSignals(True)
            dest_qspin.setValue(orig_zorder)
            dest_qspin.blockSignals(False)
            destItem = self.parent.fit[index]
            index = len(self.parent.fit)+1
      # parse extras
      if (not flag):
        for index in range(len(self.parent.extras)):
          if(self.parent.extras[index].zorder == new_zorder):
            # we found the guy
            flag = True
            dest_qspin = self.extrasTable.cellWidget(index, 1)
            # have to temporarily disable event logging
            dest_qspin.blockSignals(True)
            dest_qspin.setValue(orig_zorder)
            dest_qspin.blockSignals(False)
            destItem = self.parent.extras[index]
            index = len(self.parent.extras)+1
            
      # now swap the z-order values
      if (flag):
        # set z-order in objects to new values
        sourceItem.setZOrder(new_zorder, redraw=False)
        destItem.setZOrder(orig_zorder, redraw=False)
        
        # update legend if needed
        self.updateLegend(redraw=True)
        
  def toggleVisibilityExtras(self, index=0):
    visibilityExtra = self.extrasTable.cellWidget(index, 0)
    if (visibilityExtra.isChecked()):
      self.parent.extras[index].setVisibility(True, redraw=False)
    else:
      self.parent.extras[index].setVisibility(False, redraw=False)
    # update plot
    self.parent.plotArea.dataplotwidget.myRefresh()

  def toggleVisibilityCurve(self, index=0):
    visibilityCurve = self.curvesTable.cellWidget(index, 0)
    if (visibilityCurve.isChecked()):
      self.parent.fit[index].setVisibility(True, redraw=False)
    else:
      self.parent.fit[index].setVisibility(False, redraw=False)
    # update legend if needed
    self.updateLegend(redraw=True)

  def toggleVisibilityData(self, index=0):
    visibilityCurve = self.dataSetTable.cellWidget(index, 0)
    if (visibilityCurve.isChecked()):
      self.parent.data[index].setVisibility(True, redraw=False)
    else:
      self.parent.data[index].setVisibility(False, redraw=False)
    # update legend if needed
    self.updateLegend(redraw=True)

  def toggleVisibilityResid(self, index=0):
    visibilityResid = self.residTable.cellWidget(index, 0)
    if(index):
      index -= 1
      method = self.parent.data[index].setVisibilityResid
    else:
      method = self.parent.plotArea.setVisibilityResidLine
    if (visibilityResid.isChecked()):
      method(True)
    else:
      method(False)

  def editNameExtra(self, targetIndex=None):
    if (targetIndex != None):
      entryField = self.extrasTable.cellWidget(targetIndex, 2)
      prevName = self.parent.extras[targetIndex].labeltext
      nuName = str(entryField.text())
      valueDict = {'labeltext': nuName}
      # update label if needed
      if(prevName != nuName):
        self.parent.extras[targetIndex].setValues(valueDict, redraw=True)
 
  def editNameCurve(self, target=None, index=0):
    if (target != None):
      entryField = self.curvesTable.cellWidget(index, 3)
      prevName = target.name
      nuName = str(entryField.text())
      target.setName(nuName)
      # update legend if needed
      if(prevName != nuName):
        self.updateLegend(redraw=True)
 
  def editNameData(self, target=None, index=0):
    if (target != None):
      entryField = self.dataSetTable.cellWidget(index, 3)
      prevName = target.name
      nuName = str(entryField.text())
      target.setName(nuName)
      # update legend if needed
      if(prevName != nuName):
        self.updateLegend(redraw=True)
 
  def editNameResid(self, target=None, index=0):
    if (target != None):
      entryField = self.residTable.cellWidget(index, 3)
      target.setNameResid(str(entryField.text()))
 
  def changeResidZeroStyle(self):
    # display menu at current mouse pointer
    self.menu = ConfigMenu(self, target=self.parent.plotArea, residMode=False, residZero=True)
    # apply styles to popup window
    if(QSTYLE != None):
      self.menu.setStyle(QSTYLE)
    if(QSTYLESHEET != None):
      self.menu.setStyleSheet(QSTYLESHEET)
    # first need to display QMenu to get reliable size (even sizeHint fails)
    self.menu.popup(QtGui.QCursor.pos())
    # now move window to new position
    menuX, menuY = QtGui.QCursor.pos().x(), QtGui.QCursor.pos().y()
    menuY -= self.menu.height()
    menuY = max(menuY, 0)
    menuPos = QtCore.QPoint(menuX, menuY)
    self.menu.move(menuPos)

  def changeStyle(self, target=None, errorbar=False, residMode=False):
    # display menu at current mouse pointer
    self.menu = ConfigMenu(self, target, residMode)
    # apply styles to popup window
    if(QSTYLE != None):
      self.menu.setStyle(QSTYLE)
    if(QSTYLESHEET != None):
      self.menu.setStyleSheet(QSTYLESHEET)
    if(residMode):
      # bottom align position of QMenu
      # first need to display QMenu to get reliable size (even sizeHint fails)
      self.menu.popup(QtGui.QCursor.pos())
      # now move window to new position
      menuX, menuY = QtGui.QCursor.pos().x(), QtGui.QCursor.pos().y()
      menuY -= self.menu.height()
      menuY = max(menuY, 0)
      menuPos = QtCore.QPoint(menuX, menuY)
      self.menu.move(menuPos)
    else:
      self.menu.popup(QtGui.QCursor.pos())
    
  def changeStyleExtra(self, targetIndex=None):
    # display menu at current mouse pointer
    self.menu = ConfigMenuExtra(self, targetIndex)
    # apply styles to popup window
    if(QSTYLE != None):
      self.menu.setStyle(QSTYLE)
    if(QSTYLESHEET != None):
      self.menu.setStyleSheet(QSTYLESHEET)
    self.menu.popup(QtGui.QCursor.pos())
    
  def copyData(self, source=0):
    # this routine copies the current data set
    sourceData = self.parent.data[source].value()
    if('x' in sourceData):
      # would need some kind of deep copy to make this work ...
      # ... but copy.deepcopy produces an error due to matplotlib links, so do it manually
      self.parent.data.append(DataObject(self.parent))
      self.parent.data[-1].setName('Data_'+str(len(self.parent.data)-1))
      # need to copy contents of original object
      self.parent.data[-1].spawned(self.parent.data[source])
      # set new data object as active
      #self.parent.activeData = (len(self.parent.data) - 1)
      self.changeActiveDataSet(len(self.parent.data) - 1, setCheck=False)
      # cause data to be drawn
      self.parent.data[-1].drawMe(redraw=False)
      self.refreshDataTable()
      # also create a new resid object
      self.parent.data[-1].drawMeResid()
      self.refreshResidTable()
      # also refresh curves table to account for increased total number of items
      self.refreshCurvesTable()
      self.refreshExtrasTable()
      # update legend if needed
      self.updateLegend(redraw=True)
    else:
      self.parent.statusbar.showMessage('Data object is empty, will not copy!', self.parent.STATUS_TIME)

  def copyFit(self, source=0):
    # this routine copies the current curve
    self.parent.fit.append(FitObject(self.parent))
    self.parent.fit[-1].setName('Curve_'+str(len(self.parent.fit)-1))
    self.parent.fit[-1].retired = True
    # need to copy contents of original object
    self.parent.fit[-1].spawned(self.parent.fit[source])
    # set new curve object as active
    #self.parent.activeFit = (len(self.parent.fit) - 1)
    self.changeActiveCurve(len(self.parent.fit) - 1, redraw=False)
    # cause fxn to be drawn
    self.parent.fit[-1].drawMe(redraw=False)
    self.refreshCurvesTable()
    # also refresh data set table to account for increased total number of items
    self.refreshDataTable()
    self.refreshExtrasTable()
    # update legend if needed
    self.updateLegend(redraw=True)
    
  def copyExtra(self, source=0):
    # this routine copies the current extra
    self.parent.extras.append(ExtrasObject(self.parent))
    # need to copy contents of original object
    self.parent.extras[-1].spawned(self.parent.extras[source])
    # cause fxn to be drawn
    self.parent.extras[-1].drawMe(redraw=False)
    self.refreshExtrasTable()
    # also refresh data set table to account for increased total number of items
    self.refreshDataTable()
    self.refreshCurvesTable()
    # update legend if needed
    self.parent.plotArea.dataplotwidget.myRefresh()

  def updateLegend(self, redraw=True):
    # does legend need to be updated?
    value = self.parent.plotArea.legendVisible
    if(value or redraw):
      self.parent.plotArea.setLegend(value=value, redraw=redraw)

  def roundNumber(self, number, places=3):
    # formats number for output
    NUMBER_SWITCH = 1e3
    FORMAT_DECIMAL = '{:.' + str(places) + 'f}'
    FORMAT_SCIENTIFIC = '{:.' + str(places) + 'e}'
    # determine return string
    if((np.abs(number) > NUMBER_SWITCH) or (np.abs(number) < 1.0/NUMBER_SWITCH)):
      numberstr = FORMAT_SCIENTIFIC.format(number)
    else:
      numberstr = FORMAT_DECIMAL.format(number)

    return float(numberstr)

class ConfigMenuExtra(KuhMenu):
  def __init__(self, parent = None, targetIndex = None):
    super(ConfigMenuExtra, self).__init__()
    self.parent = parent
    self.targetIndex = targetIndex
    self.extrasType = self.parent.parent.extras[targetIndex].extrasType
    self.linestyles = ['None', 'solid', 'dashed', 'dashdot', 'dotted']
    self.dashstyles = ['butt', 'round', 'projecting']
      
    # float validator
    self.validFloat = QtGui.QDoubleValidator()

    # set up initial values (needs to be much expanded)
    if (self.targetIndex != None):
      self.style = self.parent.parent.extras[targetIndex].getStyle()
    else:
      self.style = {'x': 1, 'y': 1, 'color': [0.0, 0.0, 0.0, 1.0], 'fontsize': 12, 'fontname': 'DejaVu Sans',\
                    'rotation': 0.0, 'horizontalalignment': 'center'}

    # set up GUI
    self.buildRessource()

  def buildRessource(self):
    # build outer gui
    self.hLayout0 = QtWidgets.QHBoxLayout(self)
    self.hLayout0.setContentsMargins(*[scaledDPI(4)]*4)
    self.hLayout0.setAlignment(QtCore.Qt.AlignLeft|QtCore.Qt.AlignTop)
    
    # handle line separately -- too different from the other objects
    if(self.extrasType == 'line'):
      # build gui for line formatting
      self.formatLine = QWidgetMac()    
      self.vLayout = QtWidgets.QVBoxLayout(self.formatLine)
      self.vLayout.setContentsMargins(0, 0, 0, 0)
      self.vLayout.setAlignment(QtCore.Qt.AlignLeft|QtCore.Qt.AlignTop)
      self.hLayout0.addWidget(self.formatLine)
      
      # heading
      self.extrasStyleLabel = QtWidgets.QLabel()
      self.extrasStyleLabel.setText("<html><head/><body><span style=\"font-size:130%; font-weight:bold;\">Line</span></body></html>")
      self.vLayout.addWidget(self.extrasStyleLabel)    
      
      # line position x
      self.labelXGroup = QWidgetMac()
      self.vLayout.addWidget(self.labelXGroup)
      self.hLayout = QtWidgets.QHBoxLayout(self.labelXGroup)
      self.hLayout.setContentsMargins(0, 0, 0, 0)
      self.hLayout.setAlignment(QtCore.Qt.AlignLeft)
      self.labelXLabel = QtWidgets.QLabel('x')
      self.labelXLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.labelXLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.hLayout.addWidget(self.labelXLabel)
  
      self.labelXEntry = QLineEditClick()
      self.labelXEntry.setText(str(self.style['x']))
      self.labelXEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.labelXEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.labelXEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'x', self.labelXEntry, None, None))
      self.labelXEntry.setValidator(self.validFloat)
      self.hLayout.addWidget(self.labelXEntry)
  
      # line position y
      self.labelYGroup = QWidgetMac()
      self.vLayout.addWidget(self.labelYGroup)
      self.labelYLabel = QtWidgets.QLabel('y')
      self.labelYLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.labelYLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.hLayout.addWidget(self.labelYLabel)
  
      self.labelYEntry = QLineEditClick()
      self.labelYEntry.setText(str(self.style['y']))
      self.labelYEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.labelYEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.labelYEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'y', self.labelYEntry, None, None))
      self.labelYEntry.setValidator(self.validFloat)
      self.hLayout.addWidget(self.labelYEntry)

      # line position x2
      self.labelXGroup2 = QWidgetMac()
      self.vLayout.addWidget(self.labelXGroup2)
      self.hLayout1 = QtWidgets.QHBoxLayout(self.labelXGroup2)
      self.hLayout1.setContentsMargins(0, 0, 0, 0)
      self.hLayout1.setAlignment(QtCore.Qt.AlignLeft)
      self.labelXLabel2 = QtWidgets.QLabel('x2')
      self.labelXLabel2.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.labelXLabel2.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.hLayout1.addWidget(self.labelXLabel2)
  
      self.labelXEntry2 = QLineEditClick()
      self.labelXEntry2.setText(str(self.style['x2']))
      self.labelXEntry2.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.labelXEntry2.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.labelXEntry2.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'x2', self.labelXEntry2, None, None))
      self.labelXEntry2.setValidator(self.validFloat)
      self.hLayout1.addWidget(self.labelXEntry2)
  
      # line position y
      self.labelYGroup2 = QWidgetMac()
      self.vLayout.addWidget(self.labelYGroup2)
      self.labelYLabel2 = QtWidgets.QLabel('y2')
      self.labelYLabel2.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.labelYLabel2.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.hLayout1.addWidget(self.labelYLabel2)
  
      self.labelYEntry2 = QLineEditClick()
      self.labelYEntry2.setText(str(self.style['y2']))
      self.labelYEntry2.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.labelYEntry2.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.labelYEntry2.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'y2', self.labelYEntry2, None, None))
      self.labelYEntry2.setValidator(self.validFloat)
      self.hLayout1.addWidget(self.labelYEntry2)
      
      # line style
      self.linePropsGroup = QWidgetMac()
      self.vLayout.addWidget(self.linePropsGroup)
      self.hLayout2 = QtWidgets.QHBoxLayout(self.linePropsGroup)
      self.hLayout2.setContentsMargins(0, 0, 0, 0)
      self.hLayout2.setAlignment(QtCore.Qt.AlignLeft)
      self.linePropsLabel = QtWidgets.QLabel('Line')
      self.linePropsLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.linePropsLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.hLayout2.addWidget(self.linePropsLabel)
  
      self.lineWidthEntry = QLineEditClick()
      self.lineWidthEntry.setText(str(self.style['line__linewidth']))
      self.lineWidthEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.lineWidthEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.lineWidthEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'line__linewidth', self.lineWidthEntry, 0.0, 100.0))
      self.lineWidthEntry.setValidator(self.validFloat)
      self.hLayout2.addWidget(self.lineWidthEntry)
    
      # line color
      self.lineColorButton = QPushButtonMac()
      self.lineColorButton.setAutoFillBackground(False)
      colorvalue = [int(i*255.0) for i in self.style['line__color'][0:3]]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.lineColorButton.setStyleSheet(colorstr)
      self.lineColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.lineColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.lineColorButton.setCursor(QtCore.Qt.PointingHandCursor)
      self.lineColorButton.clicked.connect(partial(self.changeLabelColor, self.targetIndex, 'line__color'))
      self.hLayout2.addWidget(self.lineColorButton)

      # line style
      self.lineStyleGroup = QWidgetMac()
      self.vLayout.addWidget(self.lineStyleGroup)
      self.hLayout3 = QtWidgets.QHBoxLayout(self.lineStyleGroup)
      self.hLayout3.setContentsMargins(0, 0, 0, 0)
      self.hLayout3.setAlignment(QtCore.Qt.AlignLeft)
      self.lineStyleLabel = QtWidgets.QLabel('Style')
      self.lineStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.lineStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.hLayout3.addWidget(self.lineStyleLabel)

      self.lineStyle = QComboBoxMac()
      for entry in self.linestyles:
        self.lineStyle.addItem(entry)
      if(self.style['line__linestyle'] in self.linestyles):
        currindex = self.linestyles.index(self.style['line__linestyle'])
      else:
        currindex = 0
      self.lineStyle.setCurrentIndex(currindex)
      self.lineStyle.activated.connect(partial(self.changeLineStyle, self.targetIndex, 'line__linestyle', self.lineStyle))
      self.lineStyle.setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
      self.lineStyle.setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
      self.hLayout3.addWidget(self.lineStyle)
 
      # cap style
      self.comboDashStyle = QComboBoxMac()
      for entry in self.dashstyles:
        self.comboDashStyle.addItem(entry)
      if(self.style['line__dash_capstyle'] in self.dashstyles):
        currindex = self.dashstyles.index(self.style['line__dash_capstyle'])
      else:
        currindex = 0
      self.comboDashStyle.setCurrentIndex(currindex)
      self.comboDashStyle.activated.connect(partial(self.changeLineStyle, self.targetIndex, 'line__dash_capstyle', self.comboDashStyle))
      self.comboDashStyle.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
      self.comboDashStyle.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
      self.hLayout3.addWidget(self.comboDashStyle)
    else:
      # build gui for label formatting
      self.formatLabel = QWidgetMac()    
      self.vLayout = QtWidgets.QVBoxLayout(self.formatLabel)
      self.vLayout.setContentsMargins(0, 0, 0, 0)
      self.vLayout.setAlignment(QtCore.Qt.AlignLeft|QtCore.Qt.AlignTop)
      self.hLayout0.addWidget(self.formatLabel)
      
      # heading
      self.extrasStyleLabel = QtWidgets.QLabel()
      self.extrasStyleLabel.setText("<html><head/><body><span style=\"font-size:130%; font-weight:bold;\">Text</span></body></html>")
      self.vLayout.addWidget(self.extrasStyleLabel)    
      
      # label position x
      self.labelXGroup = QWidgetMac()
      self.vLayout.addWidget(self.labelXGroup)
      self.hLayout = QtWidgets.QHBoxLayout(self.labelXGroup)
      self.hLayout.setContentsMargins(0, 0, 0, 0)
      self.hLayout.setAlignment(QtCore.Qt.AlignLeft)
      self.labelXLabel = QtWidgets.QLabel('x')
      self.labelXLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.labelXLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.hLayout.addWidget(self.labelXLabel)
  
      self.labelXEntry = QLineEditClick()
      self.labelXEntry.setText(str(self.style['x']))
      self.labelXEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.labelXEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.labelXEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'x', self.labelXEntry, None, None))
      self.labelXEntry.setValidator(self.validFloat)
      self.hLayout.addWidget(self.labelXEntry)
  
      # label position y
      self.labelYGroup = QWidgetMac()
      self.vLayout.addWidget(self.labelYGroup)
      self.labelYLabel = QtWidgets.QLabel('y')
      self.labelYLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.labelYLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.hLayout.addWidget(self.labelYLabel)
  
      self.labelYEntry = QLineEditClick()
      self.labelYEntry.setText(str(self.style['y']))
      self.labelYEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.labelYEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.labelYEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'y', self.labelYEntry, None, None))
      self.labelYEntry.setValidator(self.validFloat)
      self.hLayout.addWidget(self.labelYEntry)
      
      # label text style
      self.configSizeGroup = QWidgetMac()
      self.vLayout.addWidget(self.configSizeGroup)
      self.hLayout1 = QtWidgets.QHBoxLayout(self.configSizeGroup)
      self.hLayout1.setContentsMargins(0, 0, 0, 0)
      self.hLayout1.setAlignment(QtCore.Qt.AlignLeft)
      self.configSizeLabel = QtWidgets.QLabel('Font')
      self.configSizeLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.configSizeLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.hLayout1.addWidget(self.configSizeLabel)
  
      self.configColorLabelButton = QPushButtonMac()
      self.configColorLabelButton.setAutoFillBackground(False)
      colorvalue = [int(i*255.0) for i in self.style['color'][0:3]]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.configColorLabelButton.setStyleSheet(colorstr)
      self.configColorLabelButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.configColorLabelButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.configColorLabelButton.setCursor(QtCore.Qt.PointingHandCursor)
      self.configColorLabelButton.clicked.connect(partial(self.changeLabelColor, self.targetIndex, 'color'))
      self.hLayout1.addWidget(self.configColorLabelButton)
  
      self.configLabelSize = QLineEditClick()
      self.configLabelSize.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configLabelSize.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configLabelSize.setText(str(self.style['fontsize']))
      self.configLabelSize.setValidator(self.validFloat)
      self.configLabelSize.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'fontsize', self.configLabelSize, 0.0, 100.0))
      self.hLayout1.addWidget(self.configLabelSize)
      
      self.configSizeGroup2 = QWidgetMac()
      self.vLayout.addWidget(self.configSizeGroup2)
      self.hLayout2 = QtWidgets.QHBoxLayout(self.configSizeGroup2)
      self.hLayout2.setContentsMargins(0, 0, 0, 0)
      self.hLayout2.setAlignment(QtCore.Qt.AlignLeft)
      spacer = QtWidgets.QLabel('')
      spacer.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      spacer.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.hLayout2.addWidget(spacer)
  
      defaultFont = 'DejaVu Sans'
      self.configLabelFont = QComboBoxMac()
      self.configLabelFont.addItems(self.parent.parent.fontNames)
      self.configLabelFont.setMaximumSize(QtCore.QSize(scaledDPI(140), scaledDPI(BASE_SIZE)))
      self.configLabelFont.setMinimumSize(QtCore.QSize(scaledDPI(140), scaledDPI(BASE_SIZE)))
      if(self.style['fontname'] in self.parent.parent.fontNames):
        currindex = self.parent.parent.fontNames.index(self.style['fontname'])
        self.configLabelFont.setCurrentIndex(currindex)
      elif(defaultFont in self.parent.parent.fontNames):
        currindex = self.parent.parent.fontNames.index(defaultFont)
        self.configLabelFont.setCurrentIndex(currindex)
      else:
        self.configLabelFont.setCurrentIndex(0)
      self.configLabelFont.activated.connect(partial(self.changeLabelFont, self.targetIndex))
      self.hLayout2.addWidget(self.configLabelFont)
  
      # label angle
      self.configAngleGroup = QWidgetMac()
      self.vLayout.addWidget(self.configAngleGroup)
      self.hLayout3 = QtWidgets.QHBoxLayout(self.configAngleGroup)
      self.hLayout3.setContentsMargins(0, 0, 0, 0)
      self.hLayout3.setAlignment(QtCore.Qt.AlignLeft)    
      self.configAngleLabel = QtWidgets.QLabel('Angle')
      self.configAngleLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.configAngleLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.hLayout3.addWidget(self.configAngleLabel)
  
      self.configAngle = QLineEditClick()
      self.configAngle.setText(str(self.style['rotation']))
      self.configAngle.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configAngle.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configAngle.setValidator(self.validFloat)
      self.configAngle.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'rotation', self.configAngle, 0.0, 360.0))
      self.hLayout3.addWidget(self.configAngle)
      
      # label alignment
      self.configAlignmentGroup = QWidgetMac()
      self.vLayout.addWidget(self.configAlignmentGroup)
      self.hLayout4 = QtWidgets.QHBoxLayout(self.configAlignmentGroup)
      self.hLayout4.setContentsMargins(0, 0, 0, 0)
      self.hLayout4.setAlignment(QtCore.Qt.AlignLeft)    
      self.configAlignmentLabel = QtWidgets.QLabel('Align')
      self.configAlignmentLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.configAlignmentLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.hLayout4.addWidget(self.configAlignmentLabel)
  
      self.alignHorizontal = ['left', 'center', 'right']
      self.configAlignment = QComboBoxMac()
      self.configAlignment.addItems(self.alignHorizontal)
      if(self.style['horizontalalignment'] in self.alignHorizontal):
        currindex = self.alignHorizontal.index(self.style['horizontalalignment'])
        self.configAlignment.setCurrentIndex(currindex)
      else:
        self.configAlignment.setCurrentIndex(0)
      self.configAlignment.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.configAlignment.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.configAlignment.activated.connect(partial(self.changeLabelAlignment, self.targetIndex))
      self.hLayout4.addWidget(self.configAlignment)
      
      # checkbox for display of bbox
      self.bboxShowGroup = QWidgetMac()
      self.vLayout.addWidget(self.bboxShowGroup)
      self.hLayout5 = QtWidgets.QHBoxLayout(self.bboxShowGroup)
      self.hLayout5.setContentsMargins(0, 0, 0, 0)
      self.hLayout5.setAlignment(QtCore.Qt.AlignLeft)    
      self.bboxShowLabel = QtWidgets.QLabel('Box?')
      self.bboxShowLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.bboxShowLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.hLayout5.addWidget(self.bboxShowLabel)
  
      self.bboxShowCheck = QtWidgets.QCheckBox(self.bboxShowGroup)
      self.bboxShowCheck.setGeometry(QtCore.QRect(scaledDPI(2), scaledDPI(2), scaledDPI(18), scaledDPI(18)))
      self.bboxShowCheck.setChecked(self.style['bbox__show'])
      self.bboxShowCheck.setText('')
      self.bboxShowCheck.stateChanged.connect(partial(self.toggleBbox, self.targetIndex))
      self.hLayout5.addWidget(self.bboxShowCheck)
      
      # bbox config menu
      self.divider = self.VLine()
      self.hLayout0.addWidget(self.divider)
      # build gui for label formatting
      self.formatBbox = QWidgetMac()    
      self.vLayoutA1 = QtWidgets.QVBoxLayout(self.formatBbox)
      self.vLayoutA1.setContentsMargins(0, 0, 0, 0)
      self.vLayoutA1.setAlignment(QtCore.Qt.AlignLeft|QtCore.Qt.AlignTop)
      self.hLayout0.addWidget(self.formatBbox)
        
      # heading
      self.extrasBboxLabel = QtWidgets.QLabel()
      self.extrasBboxLabel.setText("<html><head/><body><span style=\"font-size:130%; font-weight:bold;\">Box</span></body></html>")
      self.vLayoutA1.addWidget(self.extrasBboxLabel)
      
      # bbox line style
      self.bboxLineGroup = QWidgetMac()
      self.vLayoutA1.addWidget(self.bboxLineGroup)
      self.hLayoutA2 = QtWidgets.QHBoxLayout(self.bboxLineGroup)
      self.hLayoutA2.setContentsMargins(0, 0, 0, 0)
      self.hLayoutA2.setAlignment(QtCore.Qt.AlignLeft)
      self.bboxLineLabel = QtWidgets.QLabel('Line')
      self.bboxLineLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.bboxLineLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.hLayoutA2.addWidget(self.bboxLineLabel)
  
      self.bboxLineWidthEntry = QLineEditClick()
      self.bboxLineWidthEntry.setText(str(self.style['bbox__linewidth']))
      self.bboxLineWidthEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.bboxLineWidthEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.bboxLineWidthEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'bbox__linewidth', self.bboxLineWidthEntry, 0.0, 100.0))
      self.bboxLineWidthEntry.setValidator(self.validFloat)
      self.hLayoutA2.addWidget(self.bboxLineWidthEntry)
    
      self.comboBboxLineStyle = QComboBoxMac()
      for entry in self.linestyles:
        self.comboBboxLineStyle.addItem(entry)
      if(self.style['bbox__linestyle'] in self.linestyles):
        currindex = self.linestyles.index(self.style['bbox__linestyle'])
      else:
        currindex = 0
      self.comboBboxLineStyle.setCurrentIndex(currindex)
      self.comboBboxLineStyle.activated.connect(partial(self.changeLineStyle, self.targetIndex, 'bbox__linestyle', self.comboBboxLineStyle))
      self.comboBboxLineStyle.setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
      self.comboBboxLineStyle.setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
      self.hLayoutA2.addWidget(self.comboBboxLineStyle)
      
      # cap style
      self.bboxLineGroup2 = QWidgetMac()
      self.vLayoutA1.addWidget(self.bboxLineGroup2)
      self.hLayoutA22 = QtWidgets.QHBoxLayout(self.bboxLineGroup2)
      self.hLayoutA22.setContentsMargins(0, 0, 0, 0)
      self.hLayoutA22.setAlignment(QtCore.Qt.AlignLeft)
      self.bboxLineLabel2 = QtWidgets.QLabel('')
      self.bboxLineLabel2.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.bboxLineLabel2.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.hLayoutA22.addWidget(self.bboxLineLabel2)

      self.comboBboxDashStyle = QComboBoxMac()
      for entry in self.dashstyles:
        self.comboBboxDashStyle.addItem(entry)
      if(self.style['bbox__dash_capstyle'] in self.dashstyles):
        currindex = self.dashstyles.index(self.style['bbox__dash_capstyle'])
      else:
        currindex = 0
      self.comboBboxDashStyle.setCurrentIndex(currindex)
      self.comboBboxDashStyle.activated.connect(partial(self.changeLineStyle, self.targetIndex, 'bbox__dash_capstyle', self.comboBboxDashStyle))
      self.comboBboxDashStyle.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
      self.comboBboxDashStyle.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
      self.hLayoutA22.addWidget(self.comboBboxDashStyle)      
  
      # bbox colors
      self.bboxColorGroup = QWidgetMac()
      self.vLayoutA1.addWidget(self.bboxColorGroup)
      self.hLayoutA3 = QtWidgets.QHBoxLayout(self.bboxColorGroup)
      self.hLayoutA3.setContentsMargins(0, 0, 0, 0)
      self.hLayoutA3.setAlignment(QtCore.Qt.AlignLeft)
      self.bboxColorLabel = QtWidgets.QLabel('Color')
      self.bboxColorLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.bboxColorLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.hLayoutA3.addWidget(self.bboxColorLabel)
  
      self.bboxLineColorButton = QPushButtonMac()
      self.bboxLineColorButton.setAutoFillBackground(False)
      colorvalue = [int(i*255.0) for i in self.style['bbox__edgecolor'][0:3]]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.bboxLineColorButton.setStyleSheet(colorstr)
      self.bboxLineColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.bboxLineColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.bboxLineColorButton.setCursor(QtCore.Qt.PointingHandCursor)
      self.bboxLineColorButton.clicked.connect(partial(self.changeLabelColor, self.targetIndex, 'bbox__edgecolor'))
      self.hLayoutA3.addWidget(self.bboxLineColorButton)
  
      self.bboxFaceColorButton = QPushButtonMac()
      self.bboxFaceColorButton.setAutoFillBackground(False)
      colorvalue = [int(i*255.0) for i in self.style['bbox__facecolor'][0:3]]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.bboxFaceColorButton.setStyleSheet(colorstr)
      self.bboxFaceColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.bboxFaceColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.bboxFaceColorButton.setCursor(QtCore.Qt.PointingHandCursor)
      self.bboxFaceColorButton.clicked.connect(partial(self.changeLabelColor, self.targetIndex, 'bbox__facecolor'))
      self.hLayoutA3.addWidget(self.bboxFaceColorButton)    
  
      self.hatchStyles = ['', '/', '|', '-', '+', 'x', 'o', 'O', '.', '*']
      self.comboBboxHatch = QComboBoxMac()
      for entry in self.hatchStyles:
        self.comboBboxHatch.addItem(entry)
      if(self.style['bbox__hatch'] in self.hatchStyles):
        currindex = self.hatchStyles.index(self.style['bbox__hatch'])
      else:
        currindex = 0
      self.comboBboxHatch.setCurrentIndex(currindex)
      self.comboBboxHatch.activated.connect(partial(self.changeLineStyle, self.targetIndex, 'bbox__hatch', self.comboBboxHatch))
      self.comboBboxHatch.setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
      self.comboBboxHatch.setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
      self.hLayoutA3.addWidget(self.comboBboxHatch)
  
      # bbox boxstyle
      self.bboxBoxStyleGroup = QWidgetMac()
      self.vLayoutA1.addWidget(self.bboxBoxStyleGroup)
      self.hLayoutA4 = QtWidgets.QHBoxLayout(self.bboxBoxStyleGroup)
      self.hLayoutA4.setContentsMargins(0, 0, 0, 0)
      self.hLayoutA4.setAlignment(QtCore.Qt.AlignLeft)
      self.bboxBoxStyleLabel = QtWidgets.QLabel('Style')
      self.bboxBoxStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.bboxBoxStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.hLayoutA4.addWidget(self.bboxBoxStyleLabel)
  
      self.boxStyles = list(matplotlib.patches.BoxStyle.get_styles().keys())
      self.comboBboxBoxStyle = QComboBoxMac()
      for entry in self.boxStyles:
        self.comboBboxBoxStyle.addItem(entry)
      if(self.style['bbox__boxstyle'] in self.boxStyles):
        currindex = self.boxStyles.index(self.style['bbox__boxstyle'])
      else:
        currindex = 0
      self.comboBboxBoxStyle.setCurrentIndex(currindex)
      self.comboBboxBoxStyle.activated.connect(partial(self.changeLineStyle, self.targetIndex, 'bbox__boxstyle', self.comboBboxBoxStyle))
      self.comboBboxBoxStyle.setMaximumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
      self.comboBboxBoxStyle.setMinimumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
      self.hLayoutA4.addWidget(self.comboBboxBoxStyle)
      
      # bbox pad
      self.bboxPadGroup = QWidgetMac()
      self.vLayoutA1.addWidget(self.bboxPadGroup)
      self.hLayoutA5 = QtWidgets.QHBoxLayout(self.bboxPadGroup)
      self.hLayoutA5.setContentsMargins(0, 0, 0, 0)
      self.hLayoutA5.setAlignment(QtCore.Qt.AlignLeft)
      self.bboxPadLabel = QtWidgets.QLabel('Pad')
      self.bboxPadLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.bboxPadLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.hLayoutA5.addWidget(self.bboxPadLabel)
  
      self.bboxPadEntry = QLineEditClick()
      self.bboxPadEntry.setText(str(self.style['bbox__pad']))
      self.bboxPadEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.bboxPadEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.bboxPadEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'bbox__pad', self.bboxPadEntry, 0.0, 100.0))
      self.bboxPadEntry.setValidator(self.validFloat)
      self.hLayoutA5.addWidget(self.bboxPadEntry)
  
      # bbox tooth and round
      self.bboxMiscGroup = QWidgetMac()
      self.vLayoutA1.addWidget(self.bboxMiscGroup)
      self.hLayoutA6 = QtWidgets.QHBoxLayout(self.bboxMiscGroup)
      self.hLayoutA6.setContentsMargins(0, 0, 0, 0)
      self.hLayoutA6.setAlignment(QtCore.Qt.AlignLeft)
      self.bboxToothLabel = QtWidgets.QLabel('Tooth')
      self.bboxToothLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.bboxToothLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.hLayoutA6.addWidget(self.bboxToothLabel)
      self.bboxToothEntry = QLineEditClick()
      self.bboxToothEntry.setText(str(self.style['bbox__tooth_size']))
      self.bboxToothEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.bboxToothEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.bboxToothEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'bbox__tooth_size', self.bboxToothEntry, 0.0, 100.0))
      self.bboxToothEntry.setValidator(self.validFloat)
      self.hLayoutA6.addWidget(self.bboxToothEntry)
  
      self.bboxRoundingLabel = QtWidgets.QLabel('Round')
      self.bboxRoundingLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.bboxRoundingLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
      self.hLayoutA6.addWidget(self.bboxRoundingLabel)
      self.bboxRoundingEntry = QLineEditClick()
      self.bboxRoundingEntry.setText(str(self.style['bbox__rounding_size']))
      self.bboxRoundingEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.bboxRoundingEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.bboxRoundingEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'bbox__rounding_size', self.bboxRoundingEntry, 0.0, 100.0))
      self.bboxRoundingEntry.setValidator(self.validFloat)
      self.hLayoutA6.addWidget(self.bboxRoundingEntry)
  
      # annotation arrow menu
      if(self.extrasType == 'annotation'):
        blah = self.VLine()
        self.hLayout0.addWidget(blah)
        # build gui for label formatting
        self.formatArrow = QWidgetMac()    
        self.vLayoutB1 = QtWidgets.QVBoxLayout(self.formatArrow)
        self.vLayoutB1.setContentsMargins(0, 0, 0, 0)
        self.vLayoutB1.setAlignment(QtCore.Qt.AlignLeft|QtCore.Qt.AlignTop)
        self.hLayout0.addWidget(self.formatArrow)
        
        # heading
        self.extrasArrowLabel = QtWidgets.QLabel()
        self.extrasArrowLabel.setText("<html><head/><body><span style=\"font-size:130%; font-weight:bold;\">Arrow</span></body></html>")
        self.vLayoutB1.addWidget(self.extrasArrowLabel)    
  
        # arrow tip position x
        self.arrowXGroup = QWidgetMac()
        self.vLayoutB1.addWidget(self.arrowXGroup)
        self.hLayoutB1 = QtWidgets.QHBoxLayout(self.arrowXGroup)
        self.hLayoutB1.setContentsMargins(0, 0, 0, 0)
        self.hLayoutB1.setAlignment(QtCore.Qt.AlignLeft)
        self.arrowXLabel = QtWidgets.QLabel('x')
        self.arrowXLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.arrowXLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.hLayoutB1.addWidget(self.arrowXLabel)
        
        self.arrowXEntry = QLineEditClick()
        self.arrowXEntry.setText(str(self.style['arrow__x']))
        self.arrowXEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowXEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowXEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'arrow__x', self.arrowXEntry, None, None))
        self.arrowXEntry.setValidator(self.validFloat)
        self.hLayoutB1.addWidget(self.arrowXEntry)
    
        # label position y
        self.arrowYGroup = QWidgetMac()
        self.vLayoutB1.addWidget(self.arrowYGroup)
        self.arrowYLabel = QtWidgets.QLabel('y')
        self.arrowYLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.arrowYLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.hLayoutB1.addWidget(self.arrowYLabel)
    
        self.arrowYEntry = QLineEditClick()
        self.arrowYEntry.setText(str(self.style['arrow__y']))
        self.arrowYEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowYEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowYEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'arrow__y', self.arrowYEntry, None, None))
        self.arrowYEntry.setValidator(self.validFloat)
        self.hLayoutB1.addWidget(self.arrowYEntry)
      
        # arrow line style
        self.arrowLineGroup = QWidgetMac()
        self.vLayoutB1.addWidget(self.arrowLineGroup)
        self.hLayoutB2 = QtWidgets.QHBoxLayout(self.arrowLineGroup)
        self.hLayoutB2.setContentsMargins(0, 0, 0, 0)
        self.hLayoutB2.setAlignment(QtCore.Qt.AlignLeft)
        self.arrowLineLabel = QtWidgets.QLabel('Line')
        self.arrowLineLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.arrowLineLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.hLayoutB2.addWidget(self.arrowLineLabel)
  
        self.arrowLineWidthEntry = QLineEditClick()
        self.arrowLineWidthEntry.setText(str(self.style['arrow__linewidth']))
        self.arrowLineWidthEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowLineWidthEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowLineWidthEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'arrow__linewidth', self.arrowLineWidthEntry, 0.0, 100.0))
        self.arrowLineWidthEntry.setValidator(self.validFloat)
        self.hLayoutB2.addWidget(self.arrowLineWidthEntry)
    
        self.comboArrowLineStyle = QComboBoxMac()
        for entry in self.linestyles:
          self.comboArrowLineStyle.addItem(entry)
        if(self.style['arrow__linestyle'] in self.linestyles):
          currindex = self.linestyles.index(self.style['arrow__linestyle'])
        else:
          currindex = 0
        self.comboArrowLineStyle.setCurrentIndex(currindex)
        self.comboArrowLineStyle.activated.connect(partial(self.changeLineStyle, self.targetIndex, 'arrow__linestyle', self.comboArrowLineStyle))
        self.comboArrowLineStyle.setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
        self.comboArrowLineStyle.setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
        self.hLayoutB2.addWidget(self.comboArrowLineStyle)

        # cap style => once again, this setting is utterly ignored by matplotlib
        '''
        self.arrowLineGroup2 = QWidgetMac()
        self.vLayoutB1.addWidget(self.arrowLineGroup2)
        self.hLayoutB22 = QtWidgets.QHBoxLayout(self.arrowLineGroup2)
        self.hLayoutB22.setContentsMargins(0, 0, 0, 0)
        self.hLayoutB22.setAlignment(QtCore.Qt.AlignLeft)
        self.arrowLineLabel2 = QtWidgets.QLabel('')
        self.arrowLineLabel2.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.arrowLineLabel2.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.hLayoutB22.addWidget(self.arrowLineLabel2)
  
        self.comboArrowDashStyle = QComboBoxMac()
        for entry in self.dashstyles:
          self.comboArrowDashStyle.addItem(entry)
        if(self.style['arrow__dash_capstyle'] in self.dashstyles):
          currindex = self.dashstyles.index(self.style['arrow__dash_capstyle'])
        else:
          currindex = 0
        self.comboArrowDashStyle.setCurrentIndex(currindex)
        self.comboArrowDashStyle.activated.connect(partial(self.changeLineStyle, self.targetIndex, 'arrow__dash_capstyle', self.comboArrowDashStyle))
        self.comboArrowDashStyle.setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
        self.comboArrowDashStyle.setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
        self.hLayoutB22.addWidget(self.comboArrowDashStyle)
        '''
  
        # arrow colors
        self.arrowColorGroup = QWidgetMac()
        self.vLayoutB1.addWidget(self.arrowColorGroup)
        self.hLayoutB3 = QtWidgets.QHBoxLayout(self.arrowColorGroup)
        self.hLayoutB3.setContentsMargins(0, 0, 0, 0)
        self.hLayoutB3.setAlignment(QtCore.Qt.AlignLeft)
        self.arrowColorLabel = QtWidgets.QLabel('Color')
        self.arrowColorLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.arrowColorLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.hLayoutB3.addWidget(self.arrowColorLabel)
  
        self.arrowLineColorButton = QPushButtonMac()
        self.arrowLineColorButton.setAutoFillBackground(False)
        colorvalue = [int(i*255.0) for i in self.style['arrow__edgecolor'][0:3]]
        colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
        self.arrowLineColorButton.setStyleSheet(colorstr)
        self.arrowLineColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
        self.arrowLineColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
        self.arrowLineColorButton.setCursor(QtCore.Qt.PointingHandCursor)
        self.arrowLineColorButton.clicked.connect(partial(self.changeLabelColor, self.targetIndex, 'arrow__edgecolor'))
        self.hLayoutB3.addWidget(self.arrowLineColorButton)
  
        self.arrowFaceColorButton = QPushButtonMac()
        self.arrowFaceColorButton.setAutoFillBackground(False)
        colorvalue = [int(i*255.0) for i in self.style['arrow__facecolor'][0:3]]
        colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
        self.arrowFaceColorButton.setStyleSheet(colorstr)
        self.arrowFaceColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
        self.arrowFaceColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
        self.arrowFaceColorButton.setCursor(QtCore.Qt.PointingHandCursor)
        self.arrowFaceColorButton.clicked.connect(partial(self.changeLabelColor, self.targetIndex, 'arrow__facecolor'))
        self.hLayoutB3.addWidget(self.arrowFaceColorButton)
        
        self.hatchStyles = ['', '/', '|', '-', '+', 'x', 'o', 'O', '.', '*']
        self.comboArrowHatch = QComboBoxMac()
        for entry in self.hatchStyles:
          self.comboArrowHatch.addItem(entry)
        if(self.style['arrow__hatch'] in self.hatchStyles):
          currindex = self.hatchStyles.index(self.style['arrow__hatch'])
        else:
          currindex = 0
        self.comboArrowHatch.setCurrentIndex(currindex)
        self.comboArrowHatch.activated.connect(partial(self.changeLineStyle, self.targetIndex, 'arrow__hatch', self.comboArrowHatch))
        self.comboArrowHatch.setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
        self.comboArrowHatch.setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
        self.hLayoutB3.addWidget(self.comboArrowHatch)
  
        # arrow shrink
        self.arrowShrinkGroup = QWidgetMac()
        self.vLayoutB1.addWidget(self.arrowShrinkGroup)
        self.hLayoutB4 = QtWidgets.QHBoxLayout(self.arrowShrinkGroup)
        self.hLayoutB4.setContentsMargins(0, 0, 0, 0)
        self.hLayoutB4.setAlignment(QtCore.Qt.AlignLeft)
        self.arrowShrinkALabel = QtWidgets.QLabel('ShrinkA')
        self.arrowShrinkALabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.arrowShrinkALabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.hLayoutB4.addWidget(self.arrowShrinkALabel)
  
        self.arrowShrinkAEntry = QLineEditClick()
        self.arrowShrinkAEntry.setText(str(self.style['arrow__shrinkA']))
        self.arrowShrinkAEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowShrinkAEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowShrinkAEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'arrow__shrinkA', self.arrowShrinkAEntry, 0.0, 1000.0))
        self.arrowShrinkAEntry.setValidator(self.validFloat)
        self.hLayoutB4.addWidget(self.arrowShrinkAEntry)
        
        self.arrowShrinkBLabel = QtWidgets.QLabel('ShrinkB')
        self.arrowShrinkBLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.arrowShrinkBLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.hLayoutB4.addWidget(self.arrowShrinkBLabel)
  
        self.arrowShrinkBEntry = QLineEditClick()
        self.arrowShrinkBEntry.setText(str(self.style['arrow__shrinkB']))
        self.arrowShrinkBEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowShrinkBEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowShrinkBEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'arrow__shrinkB', self.arrowShrinkBEntry, 0.0, 1000.0))
        self.arrowShrinkBEntry.setValidator(self.validFloat)
        self.hLayoutB4.addWidget(self.arrowShrinkBEntry)
        
        # arrow style
        self.arrowStyleGroup = QWidgetMac()
        self.vLayoutB1.addWidget(self.arrowStyleGroup)
        self.hLayoutB5 = QtWidgets.QHBoxLayout(self.arrowStyleGroup)
        self.hLayoutB5.setContentsMargins(0, 0, 0, 0)
        self.hLayoutB5.setAlignment(QtCore.Qt.AlignLeft)
        self.arrowStyleLabel = QtWidgets.QLabel('Style')
        self.arrowStyleLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.arrowStyleLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.hLayoutB5.addWidget(self.arrowStyleLabel)
  
        self.arrowStyles = list(matplotlib.patches.ArrowStyle.get_styles().keys())
        self.comboArrowStyle = QComboBoxMac()
        for entry in self.arrowStyles:
          self.comboArrowStyle.addItem(entry)
        if(self.style['arrow__arrowstyle'] in self.arrowStyles):
          currindex = self.arrowStyles.index(self.style['arrow__arrowstyle'])
        else:
          currindex = 0
        self.comboArrowStyle.setCurrentIndex(currindex)
        self.comboArrowStyle.activated.connect(partial(self.changeLineStyle, self.targetIndex, 'arrow__arrowstyle', self.comboArrowStyle))
        self.comboArrowStyle.setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
        self.comboArrowStyle.setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
        self.hLayoutB5.addWidget(self.comboArrowStyle)
        
        # connection style
        self.arrowConnectGroup = QWidgetMac()
        self.vLayoutB1.addWidget(self.arrowConnectGroup)
        self.hLayoutB6 = QtWidgets.QHBoxLayout(self.arrowConnectGroup)
        self.hLayoutB6.setContentsMargins(0, 0, 0, 0)
        self.hLayoutB6.setAlignment(QtCore.Qt.AlignLeft)
        self.arrowConnectLabel = QtWidgets.QLabel('Connect')
        self.arrowConnectLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.arrowConnectLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.hLayoutB6.addWidget(self.arrowConnectLabel)
  
        self.connectStyles = list(matplotlib.patches.ConnectionStyle.get_styles().keys())
        if(('arc' in self.connectStyles) and ('arc3' in self.connectStyles)):
          self.connectStyles.remove('arc')
        if(('angle' in self.connectStyles) and ('angle3' in self.connectStyles)):
          self.connectStyles.remove('angle')
        self.comboConnectStyle = QComboBoxMac()
        for entry in self.connectStyles:
          self.comboConnectStyle.addItem(entry)
        if(self.style['arrow__connector'] in self.connectStyles):
          currindex = self.connectStyles.index(self.style['arrow__connector'])
        else:
          currindex = 0
        self.comboConnectStyle.setCurrentIndex(currindex)
        self.comboConnectStyle.activated.connect(partial(self.changeLineStyle, self.targetIndex, 'arrow__connector', self.comboConnectStyle))
        self.comboConnectStyle.setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
        self.comboConnectStyle.setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
        self.hLayoutB6.addWidget(self.comboConnectStyle)
  
        # arrow configuration encore
        self.arrowParamGroup1 = QWidgetMac()
        self.vLayoutB1.addWidget(self.arrowParamGroup1)
        self.hLayoutB7 = QtWidgets.QHBoxLayout(self.arrowParamGroup1)
        self.hLayoutB7.setContentsMargins(0, 0, 0, 0)
        self.hLayoutB7.setAlignment(QtCore.Qt.AlignLeft)
  
        self.arrowLengthALabel = QtWidgets.QLabel('LengthA')
        self.arrowLengthALabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.arrowLengthALabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.hLayoutB7.addWidget(self.arrowLengthALabel)
        self.arrowLengthAEntry = QLineEditClick()
        self.arrowLengthAEntry.setText(str(self.style['arrow__lengthA']))
        self.arrowLengthAEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowLengthAEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowLengthAEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'arrow__lengthA', self.arrowLengthAEntry, 0.0, 500.0))
        self.arrowLengthAEntry.setValidator(self.validFloat)
        self.hLayoutB7.addWidget(self.arrowLengthAEntry)
  
        self.arrowWidthALabel = QtWidgets.QLabel('WidthA')
        self.arrowWidthALabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.arrowWidthALabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.hLayoutB7.addWidget(self.arrowWidthALabel)
        self.arrowWidthAEntry = QLineEditClick()
        self.arrowWidthAEntry.setText(str(self.style['arrow__widthA']))
        self.arrowWidthAEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowWidthAEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowWidthAEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'arrow__widthA', self.arrowWidthAEntry, 0.0, 500.0))
        self.arrowWidthAEntry.setValidator(self.validFloat)
        self.hLayoutB7.addWidget(self.arrowWidthAEntry)
  
        self.arrowParamGroup2 = QWidgetMac()
        self.vLayoutB1.addWidget(self.arrowParamGroup2)
        self.hLayoutB8 = QtWidgets.QHBoxLayout(self.arrowParamGroup2)
        self.hLayoutB8.setContentsMargins(0, 0, 0, 0)
        self.hLayoutB8.setAlignment(QtCore.Qt.AlignLeft)
  
        self.arrowLengthBLabel = QtWidgets.QLabel('LengthB')
        self.arrowLengthBLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.arrowLengthBLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.hLayoutB8.addWidget(self.arrowLengthBLabel)
        self.arrowLengthBEntry = QLineEditClick()
        self.arrowLengthBEntry.setText(str(self.style['arrow__lengthB']))
        self.arrowLengthBEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowLengthBEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowLengthBEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'arrow__lengthB', self.arrowLengthBEntry, 0.0, 500.0))
        self.arrowLengthBEntry.setValidator(self.validFloat)
        self.hLayoutB8.addWidget(self.arrowLengthBEntry)
  
        self.arrowWidthBLabel = QtWidgets.QLabel('WidthB')
        self.arrowWidthBLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.arrowWidthBLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
        self.hLayoutB8.addWidget(self.arrowWidthBLabel)
        self.arrowWidthBEntry = QLineEditClick()
        self.arrowWidthBEntry.setText(str(self.style['arrow__widthB']))
        self.arrowWidthBEntry.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowWidthBEntry.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
        self.arrowWidthBEntry.editingFinished.connect(partial(self.changeStyle, self.targetIndex, 'arrow__widthB', self.arrowWidthBEntry, 0.0, 500.0))
        self.arrowWidthBEntry.setValidator(self.validFloat)
        self.hLayoutB8.addWidget(self.arrowWidthBEntry)

  def toggleBbox(self, targetIndex=None):
    # toggles display of bbox
    if(targetIndex != None):
      state = self.bboxShowCheck.isChecked()
      self.style['bbox__show'] = state
      self.parent.parent.extras[targetIndex].setStyle('bbox__show', state, redraw=True)
      # toggle display of bbox config menu
      if(state):
        self.formatBbox.show()
        self.divider.show()
      else:
        self.formatBbox.hide()
        self.divider.hide()
      self.adjustSize()

  def changeLabelAlignment(self, targetIndex=None):
    if(targetIndex != None):
      useAlignment = str(self.configAlignment.currentText())
      self.parent.parent.extras[targetIndex].setStyle('horizontalalignment', useAlignment, redraw=True)
    
  def changeLabelFont(self, targetIndex=None):
    if(targetIndex != None):
      useFont = str(self.configLabelFont.currentText())
      self.parent.parent.extras[targetIndex].setStyle('fontname', useFont, redraw=True)
    
  def changeLabelColor(self, targetIndex=None, key=None):
    # colors the text element
    if((targetIndex != None) and (key in self.style)):
      # get current color
      prevColor = [255*i for i in self.style[key]]
      prevColor = QtGui.QColor(*prevColor)
      # call QColor dialog
      nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
      if (nuColor.isValid()):
        value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
        value = [i/255.0 for i in value]
        self.parent.parent.extras[targetIndex].setStyle(key, value, redraw=True)

  def changeStyle(self, targetIndex=None, key=None, entryfield=None, minval=0, maxval=1):
    if((targetIndex != None) and (key != None)):
      # check paramter boundaries
      try:
        value = float(entryfield.text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      if(maxval != None):
        value = np.min((value, maxval))
      if(minval != None):
        value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        entryfield.setText(str(value))
      if(key in self.style):
        self.style[key] = value
        self.parent.parent.extras[targetIndex].setStyle(key, value, redraw=True)

  def changeLineStyle(self, targetIndex=None, key=None, entryfield=None, minval=0, maxval=1):
    if((targetIndex != None) and (key != None)):
      # check paramter boundaries
      value = str(entryfield.currentText())
      if(key in self.style):
        self.style[key] = value
        self.parent.parent.extras[targetIndex].setStyle(key, value, redraw=True)

  def VLine(self):
    # draws a vertical line
    vline = QtWidgets.QFrame()
    vline.setFrameShape(QtWidgets.QFrame.VLine)
    vline.setFrameShadow(QtWidgets.QFrame.Sunken)
    return vline

class ConfigMenu(KuhMenu):
  def __init__(self, parent = None, target = None, residMode = False, residZero = False):
    super(ConfigMenu, self).__init__()
    self.parent = parent
    self.target = target
    self.residMode = residMode
    self.residZero = residZero
      
    # set up GUI
    self.buildRessource()
    
  def buildRessource(self):
    # build gui
    self.vLayout = QtWidgets.QVBoxLayout(self)
    self.vLayout.setContentsMargins(*[scaledDPI(4)]*4)
    self.upperRow = QWidgetMac()
    self.vLayout.addWidget(self.upperRow)

    self.hLayout = QtWidgets.QHBoxLayout(self.upperRow)
    self.hLayout.setContentsMargins(0, 0, 0, 0)
    
    # populate menu with items
    # set up line style configurator
    self.lineStyleMenu = lineStyleMenu(self, self.target, self.residMode, self.residZero)
    self.hLayout.addWidget(self.lineStyleMenu)
    
    if(not self.residZero):
      # set up marker style configurator
      self.hLayout.addWidget(self.VLine())
      self.markerStyleMenu = markerStyleMenu(self, self.target, self.residMode)
      self.hLayout.addWidget(self.markerStyleMenu)
      self.hLayout.addStretch()

    if((self.target in self.parent.parent.data) and (not self.residMode)):
      # generate lower row
      self.vLayout.addWidget(self.HLine())
      self.lowerRow = QWidgetMac()
      self.vLayout.addWidget(self.lowerRow)
      self.hLayout2 = QtWidgets.QHBoxLayout(self.lowerRow)
      self.hLayout2.setContentsMargins(0, 0, 0, 0)

      # set up bar style configurator
      self.barStyleMenu = barStyleMenu(self, self.target, self.residMode)
      self.hLayout2.addWidget(self.barStyleMenu)

      # set up stack style configurator
      self.hLayout2.addWidget(self.VLine())
      self.stackStyleMenu = stackStyleMenu(self, self.target, self.residMode)
      self.hLayout2.addWidget(self.stackStyleMenu)
  
      # set up errorbar configurator
      self.hLayout2.addWidget(self.VLine())
      self.errorStyleMenu = errorStyleMenu(self, self.target, self.residMode)
      self.hLayout2.addWidget(self.errorStyleMenu)

  def HLine(self):
    # draws a horizontal line
    hline = QtWidgets.QFrame()
    hline.setFrameShape(QtWidgets.QFrame.HLine)
    hline.setFrameShadow(QtWidgets.QFrame.Sunken)
    return hline

  def VLine(self):
    # draws a vertical line
    vline = QtWidgets.QFrame()
    vline.setFrameShape(QtWidgets.QFrame.VLine)
    vline.setFrameShadow(QtWidgets.QFrame.Sunken)
    return vline

class GraphicsArea(QWidgetMac):
  def __init__(self, parent = None):
    super(GraphicsArea, self).__init__()
    self.parent = parent
    
    # float validator
    self.validFloat = QtGui.QDoubleValidator()
    
    # set up GUI
    self.buildRessource()
    # now populate fields
    self.updateFields(initialize=True)
    # and connect events
    self.connectEvents()

  def buildRessource(self):
    # build gui
    self.vLayout_0 = QtWidgets.QVBoxLayout(self)
    self.vLayout_0.setContentsMargins(0, 0, 0, 0)
    self.vLayout_0.setAlignment(QtCore.Qt.AlignTop)
    
    # container widget for subsequent widgets
    self.containerScroll = QtWidgets.QScrollArea()
    self.containerScroll.setWidgetResizable(True)
    # don't use palettes as these are incompatible with style sheets
    self.containerScroll.setAutoFillBackground(True)
    self.vLayout_0.addWidget(self.containerScroll)

    self.containerBox = QWidgetMac()
    self.containerBox.setObjectName('stultus')
    # setting the background somehow breaks QStyleSet for children :(
    #self.containerBox.setStyleSheet('#stultus {background-color: white;}')
    self.containerBox.setAutoFillBackground(True)
    self.vLayout = QtWidgets.QVBoxLayout(self.containerBox)
    self.vLayout.setContentsMargins(0, 0, 0, 0)
    self.vLayout.setAlignment(QtCore.Qt.AlignLeft)
    self.containerScroll.setWidget(self.containerBox)
    
    # x label config
    self.configXBox = QWidgetMac()
    self.vLayout.addWidget(self.configXBox)
    self.Layout_configX = QtWidgets.QHBoxLayout(self.configXBox)
    self.Layout_configX.setContentsMargins(0, 0, 0, 0)
    self.Layout_configX.setAlignment(QtCore.Qt.AlignLeft)
    self.configXLabel = QtWidgets.QLabel()
    self.configXLabel.setText("<html><head/><body><span style=\"font-weight:bold;\">xlabel</span></body></html>")
    self.configXLabel.setMaximumSize(QtCore.QSize(scaledDPI(31), scaledDPI(BASE_SIZE)))
    self.configXLabel.setMinimumSize(QtCore.QSize(scaledDPI(31), scaledDPI(BASE_SIZE)))
    self.Layout_configX.addWidget(self.configXLabel)
    self.configXName = QLineEditClick()
    self.configXName.setMaximumSize(QtCore.QSize(scaledDPI(100), scaledDPI(BASE_SIZE)))
    self.configXName.setMinimumSize(QtCore.QSize(scaledDPI(100), scaledDPI(BASE_SIZE)))
    self.Layout_configX.addWidget(self.configXName)

    self.configXSizeLabel = QtWidgets.QLabel('font')
    self.configXSizeLabel.setMaximumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.configXSizeLabel.setMinimumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.Layout_configX.addWidget(self.configXSizeLabel)
    self.configXColorButton = QPushButtonMac()
    self.configXColorButton.setAutoFillBackground(False)
    self.configXColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configXColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configXColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.Layout_configX.addWidget(self.configXColorButton)

    self.configXSize = QLineEditClick()
    self.configXSize.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configXSize.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configXSize.setValidator(self.validFloat)
    self.Layout_configX.addWidget(self.configXSize)
    
    self.configXFont = QComboBoxMac()
    self.configXFont.addItems(self.parent.fontNames)
    self.configXFont.setMaximumSize(QtCore.QSize(scaledDPI(140), scaledDPI(BASE_SIZE)))
    self.configXFont.setMinimumSize(QtCore.QSize(scaledDPI(140), scaledDPI(BASE_SIZE)))
    self.Layout_configX.addWidget(self.configXFont)

    # x label config 2nd line
    self.configXBox2 = QWidgetMac()
    self.vLayout.addWidget(self.configXBox2)
    self.Layout_configX2 = QtWidgets.QHBoxLayout(self.configXBox2)
    self.Layout_configX2.setContentsMargins(0, 0, 0, 0)
    self.Layout_configX2.setAlignment(QtCore.Qt.AlignLeft)

    spacer = QtWidgets.QLabel()
    spacer.setMaximumSize(QtCore.QSize(scaledDPI(1), scaledDPI(BASE_SIZE)))
    spacer.setMinimumSize(QtCore.QSize(scaledDPI(1), scaledDPI(BASE_SIZE)))
    self.Layout_configX2.addWidget(spacer)
    
    self.configXAngleLabel = QtWidgets.QLabel('angle')
    self.configXAngleLabel.setMaximumSize(QtCore.QSize(scaledDPI(26), scaledDPI(BASE_SIZE)))
    self.configXAngleLabel.setMinimumSize(QtCore.QSize(scaledDPI(26), scaledDPI(BASE_SIZE)))
    self.Layout_configX2.addWidget(self.configXAngleLabel)

    self.configXAngle = QLineEditClick()
    self.configXAngle.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configXAngle.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configXAngle.setValidator(self.validFloat)
    self.Layout_configX2.addWidget(self.configXAngle)
    
    self.configXAlignmentLabel = QtWidgets.QLabel('align')
    self.configXAlignmentLabel.setMaximumSize(QtCore.QSize(scaledDPI(22), scaledDPI(BASE_SIZE)))
    self.configXAlignmentLabel.setMinimumSize(QtCore.QSize(scaledDPI(22), scaledDPI(BASE_SIZE)))
    self.Layout_configX2.addWidget(self.configXAlignmentLabel)

    self.alignHorizontal = ['left', 'center', 'right']
    self.configXAlignment = QComboBoxMac()
    self.configXAlignment.addItems(self.alignHorizontal)
    self.configXAlignment.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.configXAlignment.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.Layout_configX2.addWidget(self.configXAlignment)

    self.configXPosLabel = QtWidgets.QLabel('pos.')
    self.configXPosLabel.setMaximumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.configXPosLabel.setMinimumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.Layout_configX2.addWidget(self.configXPosLabel)

    self.configXPos = QLineEditClick()
    self.configXPos.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configXPos.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configXPos.setValidator(self.validFloat)
    self.Layout_configX2.addWidget(self.configXPos)

    self.configXPadLabel = QtWidgets.QLabel('pad')
    self.configXPadLabel.setMaximumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.configXPadLabel.setMinimumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.Layout_configX2.addWidget(self.configXPadLabel)

    self.configXPad = QLineEditClick()
    self.configXPad.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configXPad.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configXPad.setValidator(self.validFloat)
    self.Layout_configX2.addWidget(self.configXPad)

    # y label config
    self.configYBox = QWidgetMac()
    self.vLayout.addWidget(self.configYBox)
    self.Layout_configY = QtWidgets.QHBoxLayout(self.configYBox)
    self.Layout_configY.setContentsMargins(0, 0, 0, 0)
    self.Layout_configY.setAlignment(QtCore.Qt.AlignLeft)
    self.configYLabel = QtWidgets.QLabel()
    self.configYLabel.setText("<html><head/><body><span style=\"font-weight:bold;\">ylabel</span></body></html>")
    self.configYLabel.setMaximumSize(QtCore.QSize(scaledDPI(31), scaledDPI(BASE_SIZE)))
    self.configYLabel.setMinimumSize(QtCore.QSize(scaledDPI(31), scaledDPI(BASE_SIZE)))
    self.Layout_configY.addWidget(self.configYLabel)
    self.configYName = QLineEditClick()
    self.configYName.setMaximumSize(QtCore.QSize(scaledDPI(100), scaledDPI(BASE_SIZE)))
    self.configYName.setMinimumSize(QtCore.QSize(scaledDPI(100), scaledDPI(BASE_SIZE)))
    self.Layout_configY.addWidget(self.configYName)

    self.configYSizeLabel = QtWidgets.QLabel('font')
    self.configYSizeLabel.setMaximumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.configYSizeLabel.setMinimumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.Layout_configY.addWidget(self.configYSizeLabel)
    self.configYColorButton = QPushButtonMac()
    self.configYColorButton.setAutoFillBackground(False)
    self.configYColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configYColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configYColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.Layout_configY.addWidget(self.configYColorButton)

    self.configYSize = QLineEditClick()
    self.configYSize.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configYSize.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configYSize.setValidator(self.validFloat)
    self.Layout_configY.addWidget(self.configYSize)

    self.configYFont = QComboBoxMac()
    self.configYFont.addItems(self.parent.fontNames)
    self.configYFont.setMaximumSize(QtCore.QSize(scaledDPI(140), scaledDPI(BASE_SIZE)))
    self.configYFont.setMinimumSize(QtCore.QSize(scaledDPI(140), scaledDPI(BASE_SIZE)))
    self.Layout_configY.addWidget(self.configYFont)

    # y label config 2nd line
    self.configYBox2 = QWidgetMac()
    self.vLayout.addWidget(self.configYBox2)
    self.Layout_configY2 = QtWidgets.QHBoxLayout(self.configYBox2)
    self.Layout_configY2.setContentsMargins(0, 0, 0, 0)
    self.Layout_configY2.setAlignment(QtCore.Qt.AlignLeft)

    spacer = QtWidgets.QLabel()
    spacer.setMaximumSize(QtCore.QSize(scaledDPI(1), scaledDPI(BASE_SIZE)))
    spacer.setMinimumSize(QtCore.QSize(scaledDPI(1), scaledDPI(BASE_SIZE)))
    self.Layout_configY2.addWidget(spacer)
    
    self.configYAngleLabel = QtWidgets.QLabel('angle')
    self.configYAngleLabel.setMaximumSize(QtCore.QSize(scaledDPI(26), scaledDPI(BASE_SIZE)))
    self.configYAngleLabel.setMinimumSize(QtCore.QSize(scaledDPI(26), scaledDPI(BASE_SIZE)))
    self.Layout_configY2.addWidget(self.configYAngleLabel)

    self.configYAngle = QLineEditClick()
    self.configYAngle.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configYAngle.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configYAngle.setValidator(self.validFloat)
    self.Layout_configY2.addWidget(self.configYAngle)
    
    self.configYAlignmentLabel = QtWidgets.QLabel('align')
    self.configYAlignmentLabel.setMaximumSize(QtCore.QSize(scaledDPI(22), scaledDPI(BASE_SIZE)))
    self.configYAlignmentLabel.setMinimumSize(QtCore.QSize(scaledDPI(22), scaledDPI(BASE_SIZE)))
    self.Layout_configY2.addWidget(self.configYAlignmentLabel)

    self.alignVertical = ['left', 'center', 'right']
    self.configYAlignment = QComboBoxMac()
    self.configYAlignment.addItems(self.alignVertical)
    self.configYAlignment.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.configYAlignment.setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.Layout_configY2.addWidget(self.configYAlignment)

    self.configYPosLabel = QtWidgets.QLabel('pos.')
    self.configYPosLabel.setMaximumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.configYPosLabel.setMinimumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.Layout_configY2.addWidget(self.configYPosLabel)

    self.configYPos = QLineEditClick()
    self.configYPos.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configYPos.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configYPos.setValidator(self.validFloat)
    self.Layout_configY2.addWidget(self.configYPos)

    self.configYPadLabel = QtWidgets.QLabel('pad')
    self.configYPadLabel.setMaximumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.configYPadLabel.setMinimumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.Layout_configY2.addWidget(self.configYPadLabel)

    self.configYPad = QLineEditClick()
    self.configYPad.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configYPad.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configYPad.setValidator(self.validFloat)
    self.Layout_configY2.addWidget(self.configYPad)

    # axis config
    blah = self.HLine()
    self.vLayout.addWidget(blah)
    self.linestyles = ['None', 'solid', 'dashed', 'dashdot', 'dotted']
    self.dashstyles = ['butt', 'round', 'projecting']
    self.configAxisBox = {}; self.Layout_configAxis = {}
    self.configAxisLabel = {}; self.configAxisCheck = {}
    self.configAxisWidthLabel = {}; self.configAxisWidth = {}
    self.configAxisStyle = {}; self.configAxisDashStyle = {}; self.configAxisColor = {}
    for axis in ['bottom', 'top', 'left', 'right']:
      self.configAxisBox[axis] = QWidgetMac()
      self.vLayout.addWidget(self.configAxisBox[axis])
      self.Layout_configAxis[axis] = QtWidgets.QHBoxLayout(self.configAxisBox[axis])
      self.Layout_configAxis[axis].setContentsMargins(0, 0, 0, 0)
      self.Layout_configAxis[axis].setAlignment(QtCore.Qt.AlignLeft)
      self.configAxisLabel[axis] = QtWidgets.QLabel()
      self.configAxisLabel[axis].setText("<html><head/><body><span style=\"font-weight:bold;\">ax " + axis + "</span></body></html>")
      self.configAxisLabel[axis].setMaximumSize(QtCore.QSize(scaledDPI(54), scaledDPI(BASE_SIZE)))
      self.configAxisLabel[axis].setMinimumSize(QtCore.QSize(scaledDPI(54), scaledDPI(BASE_SIZE)))
      self.Layout_configAxis[axis].addWidget(self.configAxisLabel[axis])
      self.configAxisCheck[axis] = QtWidgets.QCheckBox()
      self.configAxisCheck[axis].setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 8), scaledDPI(BASE_SIZE - 8)))
      self.Layout_configAxis[axis].addWidget(self.configAxisCheck[axis])

      self.configAxisColor[axis] = QPushButtonMac()
      self.configAxisColor[axis].setAutoFillBackground(False)
      self.configAxisColor[axis].setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.configAxisColor[axis].setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.configAxisColor[axis].setCursor(QtCore.Qt.PointingHandCursor)
      self.Layout_configAxis[axis].addWidget(self.configAxisColor[axis])
  
      self.configAxisWidthLabel[axis] = QtWidgets.QLabel('width')
      self.configAxisWidthLabel[axis].setMinimumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
      self.configAxisWidthLabel[axis].setMaximumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
      self.Layout_configAxis[axis].addWidget(self.configAxisWidthLabel[axis])
      self.configAxisWidth[axis] = QLineEditClick()
      self.configAxisWidth[axis].setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configAxisWidth[axis].setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configAxisWidth[axis].setValidator(self.validFloat)
      self.Layout_configAxis[axis].addWidget(self.configAxisWidth[axis])

      self.configAxisStyle[axis] = QComboBoxMac()
      self.configAxisStyle[axis].setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
      self.Layout_configAxis[axis].addWidget(self.configAxisStyle[axis])

      self.configAxisDashStyle[axis] = QComboBoxMac()
      self.configAxisDashStyle[axis].setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
      self.configAxisDashStyle[axis].setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
      self.Layout_configAxis[axis].addWidget(self.configAxisDashStyle[axis])
      
    # arrow config
    blah = self.HLine()
    self.vLayout.addWidget(blah)
    self.configArrowBox = {}; self.Layout_configArrow = {}
    self.configArrowLabel = {}; self.configArrowCheck = {}
    self.configArrowLineColor = {}; self.configArrowFillColor = {}
    self.configArrowHeadLengthLabel = {}; self.configArrowHeadLength = {}
    self.configArrowHeadWidthLabel = {}; self.configArrowHeadWidth = {}
    self.configArrowOverhangLabel = {}; self.configArrowOverhang = {}
    self.configArrowOffsetLabel = {}; self.configArrowOffset = {}
    for axis in ['x', 'y']:
      self.configArrowBox[axis] = QWidgetMac()
      self.vLayout.addWidget(self.configArrowBox[axis])
      self.Layout_configArrow[axis] = QtWidgets.QHBoxLayout(self.configArrowBox[axis])
      self.Layout_configArrow[axis].setContentsMargins(0, 0, 0, 0)
      self.Layout_configArrow[axis].setAlignment(QtCore.Qt.AlignLeft)
      
      self.configArrowLabel[axis] = QtWidgets.QLabel()
      self.configArrowLabel[axis].setText("<html><head/><body><span style=\"font-weight:bold;\">arrow " + axis + "</span></body></html>")
      self.configArrowLabel[axis].setMaximumSize(QtCore.QSize(scaledDPI(40), scaledDPI(BASE_SIZE)))
      self.configArrowLabel[axis].setMinimumSize(QtCore.QSize(scaledDPI(40), scaledDPI(BASE_SIZE)))
      self.Layout_configArrow[axis].addWidget(self.configArrowLabel[axis])
      self.configArrowCheck[axis] = QtWidgets.QCheckBox()
      self.configArrowCheck[axis].setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 8), scaledDPI(BASE_SIZE - 8)))
      self.Layout_configArrow[axis].addWidget(self.configArrowCheck[axis])

      self.configArrowLineColor[axis] = QPushButtonMac()
      self.configArrowLineColor[axis].setAutoFillBackground(False)
      self.configArrowLineColor[axis].setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.configArrowLineColor[axis].setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.configArrowLineColor[axis].setCursor(QtCore.Qt.PointingHandCursor)
      self.Layout_configArrow[axis].addWidget(self.configArrowLineColor[axis])
      self.configArrowFillColor[axis] = QPushButtonMac()
      self.configArrowFillColor[axis].setAutoFillBackground(False)
      self.configArrowFillColor[axis].setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.configArrowFillColor[axis].setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.configArrowFillColor[axis].setCursor(QtCore.Qt.PointingHandCursor)
      self.Layout_configArrow[axis].addWidget(self.configArrowFillColor[axis])
  
      self.configArrowHeadLengthLabel[axis] = QtWidgets.QLabel('length')
      self.configArrowHeadLengthLabel[axis].setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configArrowHeadLengthLabel[axis].setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.Layout_configArrow[axis].addWidget(self.configArrowHeadLengthLabel[axis])
      self.configArrowHeadLength[axis] = QLineEditClick()
      self.configArrowHeadLength[axis].setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configArrowHeadLength[axis].setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configArrowHeadLength[axis].setValidator(self.validFloat)
      self.Layout_configArrow[axis].addWidget(self.configArrowHeadLength[axis])
      self.configArrowHeadWidthLabel[axis] = QtWidgets.QLabel('width')
      self.configArrowHeadWidthLabel[axis].setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configArrowHeadWidthLabel[axis].setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.Layout_configArrow[axis].addWidget(self.configArrowHeadWidthLabel[axis])
      self.configArrowHeadWidth[axis] = QLineEditClick()
      self.configArrowHeadWidth[axis].setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configArrowHeadWidth[axis].setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configArrowHeadWidth[axis].setValidator(self.validFloat)
      self.Layout_configArrow[axis].addWidget(self.configArrowHeadWidth[axis])

      self.configArrowOverhangLabel[axis] = QtWidgets.QLabel('ind.')
      self.configArrowOverhangLabel[axis].setMinimumSize(QtCore.QSize(scaledDPI(16), scaledDPI(BASE_SIZE)))
      self.configArrowOverhangLabel[axis].setMaximumSize(QtCore.QSize(scaledDPI(16), scaledDPI(BASE_SIZE)))
      self.Layout_configArrow[axis].addWidget(self.configArrowOverhangLabel[axis])
      self.configArrowOverhang[axis] = QLineEditClick()
      self.configArrowOverhang[axis].setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configArrowOverhang[axis].setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configArrowOverhang[axis].setValidator(self.validFloat)
      self.Layout_configArrow[axis].addWidget(self.configArrowOverhang[axis])

      self.configArrowOffsetLabel[axis] = QtWidgets.QLabel('off.')
      self.configArrowOffsetLabel[axis].setMinimumSize(QtCore.QSize(scaledDPI(16), scaledDPI(BASE_SIZE)))
      self.configArrowOffsetLabel[axis].setMaximumSize(QtCore.QSize(scaledDPI(16), scaledDPI(BASE_SIZE)))
      self.Layout_configArrow[axis].addWidget(self.configArrowOffsetLabel[axis])
      self.configArrowOffset[axis] = QLineEditClick()
      self.configArrowOffset[axis].setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configArrowOffset[axis].setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configArrowOffset[axis].setValidator(self.validFloat)
      self.Layout_configArrow[axis].addWidget(self.configArrowOffset[axis])

    # x ticks config
    blah = self.HLine()
    self.vLayout.addWidget(blah)
    self.configTickXBox = QWidgetMac()
    self.vLayout.addWidget(self.configTickXBox)
    self.Layout_configTickX = QtWidgets.QHBoxLayout(self.configTickXBox)
    self.Layout_configTickX.setContentsMargins(0, 0, 0, 0)
    self.Layout_configTickX.setAlignment(QtCore.Qt.AlignLeft)
    self.configTickXLabel = QtWidgets.QLabel()
    self.configTickXLabel.setText("<html><head/><body><span style=\"font-weight:bold;\">x ticks</span></body></html>")
    self.configTickXLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
    self.configTickXLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
    self.Layout_configTickX.addWidget(self.configTickXLabel)
    
    self.configTickXAuto = QPushButtonMac()
    self.configTickXAuto.setText('auto')
    self.configTickXAuto.setMaximumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
    self.configTickXAuto.setMinimumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
    self.Layout_configTickX.addWidget(self.configTickXAuto)
        
    self.configTickXEntry = QLineEditClick()
    self.configTickXEntry.setMaximumSize(QtCore.QSize(scaledDPI(150), scaledDPI(BASE_SIZE)))
    self.configTickXEntry.setMinimumSize(QtCore.QSize(scaledDPI(150), scaledDPI(BASE_SIZE)))
    self.Layout_configTickX.addWidget(self.configTickXEntry)

    self.configTickUseData = QPushButtonMac()
    self.configTickUseData.setText('use labels')
    self.configTickUseData.setMaximumSize(QtCore.QSize(scaledDPI(55), scaledDPI(BASE_SIZE)))
    self.configTickUseData.setMinimumSize(QtCore.QSize(scaledDPI(55), scaledDPI(BASE_SIZE)))
    self.Layout_configTickX.addWidget(self.configTickUseData)

    self.configTickXBox2 = QWidgetMac()
    self.vLayout.addWidget(self.configTickXBox2)
    self.Layout_configTickX2 = QtWidgets.QHBoxLayout(self.configTickXBox2)
    self.Layout_configTickX2.setContentsMargins(0, 0, 0, 0)
    self.Layout_configTickX2.setAlignment(QtCore.Qt.AlignLeft)

    spacer = QtWidgets.QLabel()
    spacer.setMaximumSize(QtCore.QSize(scaledDPI(4), scaledDPI(BASE_SIZE)))
    spacer.setMinimumSize(QtCore.QSize(scaledDPI(4), scaledDPI(BASE_SIZE)))
    self.Layout_configTickX2.addWidget(spacer)
    
    self.configTickXAngleLabel = QtWidgets.QLabel('angle')
    self.configTickXAngleLabel.setMaximumSize(QtCore.QSize(scaledDPI(26), scaledDPI(BASE_SIZE)))
    self.configTickXAngleLabel.setMinimumSize(QtCore.QSize(scaledDPI(26), scaledDPI(BASE_SIZE)))
    self.Layout_configTickX2.addWidget(self.configTickXAngleLabel)

    self.configTickXAngle = QLineEditClick()
    self.configTickXAngle.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configTickXAngle.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configTickXAngle.setValidator(self.validFloat)
    self.Layout_configTickX2.addWidget(self.configTickXAngle)
    
    self.configTickXSizeLabel = QtWidgets.QLabel('font')
    self.configTickXSizeLabel.setMaximumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.configTickXSizeLabel.setMinimumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.Layout_configTickX2.addWidget(self.configTickXSizeLabel)
    self.configTickXColorButton = QPushButtonMac()
    self.configTickXColorButton.setAutoFillBackground(False)
    self.configTickXColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configTickXColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configTickXColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.Layout_configTickX2.addWidget(self.configTickXColorButton)

    self.configTickXSize = QLineEditClick()
    self.configTickXSize.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configTickXSize.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configTickXSize.setValidator(self.validFloat)
    self.Layout_configTickX2.addWidget(self.configTickXSize)

    self.configTickXFont = QComboBoxMac()
    self.configTickXFont.addItems(self.parent.fontNames)
    self.configTickXFont.setMaximumSize(QtCore.QSize(scaledDPI(150), scaledDPI(BASE_SIZE)))
    self.configTickXFont.setMinimumSize(QtCore.QSize(scaledDPI(150), scaledDPI(BASE_SIZE)))
    self.Layout_configTickX2.addWidget(self.configTickXFont)

    # y ticks config
    self.configTickYBox = QWidgetMac()
    self.vLayout.addWidget(self.configTickYBox)
    self.Layout_configTickY = QtWidgets.QHBoxLayout(self.configTickYBox)
    self.Layout_configTickY.setContentsMargins(0, 0, 0, 0)
    self.Layout_configTickY.setAlignment(QtCore.Qt.AlignLeft)
    self.configTickYLabel = QtWidgets.QLabel()
    self.configTickYLabel.setText("<html><head/><body><span style=\"font-weight:bold;\">y ticks</span></body></html>")
    self.configTickYLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
    self.configTickYLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
    self.Layout_configTickY.addWidget(self.configTickYLabel)
    
    self.configTickYAuto = QPushButtonMac()
    self.configTickYAuto.setText('auto')
    self.configTickYAuto.setMaximumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
    self.configTickYAuto.setMinimumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
    self.Layout_configTickY.addWidget(self.configTickYAuto)
        
    self.configTickYEntry = QLineEditClick()
    self.configTickYEntry.setMaximumSize(QtCore.QSize(scaledDPI(150), scaledDPI(BASE_SIZE)))
    self.configTickYEntry.setMinimumSize(QtCore.QSize(scaledDPI(150), scaledDPI(BASE_SIZE)))
    self.Layout_configTickY.addWidget(self.configTickYEntry)

    self.configTickYBox2 = QWidgetMac()
    self.vLayout.addWidget(self.configTickYBox2)
    self.Layout_configTickY2 = QtWidgets.QHBoxLayout(self.configTickYBox2)
    self.Layout_configTickY2.setContentsMargins(0, 0, 0, 0)
    self.Layout_configTickY2.setAlignment(QtCore.Qt.AlignLeft)

    spacer = QtWidgets.QLabel()
    spacer.setMaximumSize(QtCore.QSize(scaledDPI(4), scaledDPI(BASE_SIZE)))
    spacer.setMinimumSize(QtCore.QSize(scaledDPI(4), scaledDPI(BASE_SIZE)))
    self.Layout_configTickY2.addWidget(spacer)

    self.configTickYAngleLabel = QtWidgets.QLabel('angle')
    self.configTickYAngleLabel.setMaximumSize(QtCore.QSize(scaledDPI(26), scaledDPI(BASE_SIZE)))
    self.configTickYAngleLabel.setMinimumSize(QtCore.QSize(scaledDPI(26), scaledDPI(BASE_SIZE)))
    self.Layout_configTickY2.addWidget(self.configTickYAngleLabel)

    self.configTickYAngle = QLineEditClick()
    self.configTickYAngle.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configTickYAngle.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configTickYAngle.setValidator(self.validFloat)
    self.Layout_configTickY2.addWidget(self.configTickYAngle)
    
    self.configTickYSizeLabel = QtWidgets.QLabel('font')
    self.configTickYSizeLabel.setMaximumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.configTickYSizeLabel.setMinimumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.Layout_configTickY2.addWidget(self.configTickYSizeLabel)
    self.configTickYColorButton = QPushButtonMac()
    self.configTickYColorButton.setAutoFillBackground(False)
    self.configTickYColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configTickYColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configTickYColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.Layout_configTickY2.addWidget(self.configTickYColorButton)

    self.configTickYSize = QLineEditClick()
    self.configTickYSize.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configTickYSize.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configTickYSize.setValidator(self.validFloat)
    self.Layout_configTickY2.addWidget(self.configTickYSize)

    self.configTickYFont = QComboBoxMac()
    self.configTickYFont.addItems(self.parent.fontNames)
    self.configTickYFont.setMaximumSize(QtCore.QSize(scaledDPI(150), scaledDPI(BASE_SIZE)))
    self.configTickYFont.setMinimumSize(QtCore.QSize(scaledDPI(150), scaledDPI(BASE_SIZE)))
    self.Layout_configTickY2.addWidget(self.configTickYFont)

    self.configTickResidYBox = QWidgetMac()
    self.vLayout.addWidget(self.configTickResidYBox)
    self.Layout_configTickResidY = QtWidgets.QHBoxLayout(self.configTickResidYBox)
    self.Layout_configTickResidY.setContentsMargins(0, 0, 0, 0)
    self.Layout_configTickResidY.setAlignment(QtCore.Qt.AlignLeft)
    self.configTickResidYLabel = QtWidgets.QLabel()
    self.configTickResidYLabel.setText("<html><head/><body><span style=\"font-weight:bold;\">resid</span></body></html>")
    self.configTickResidYLabel.setMaximumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
    self.configTickResidYLabel.setMinimumSize(QtCore.QSize(scaledDPI(35), scaledDPI(BASE_SIZE)))
    self.Layout_configTickResidY.addWidget(self.configTickResidYLabel)

    self.configTickResidYAuto = QPushButtonMac()
    self.configTickResidYAuto.setText('auto')
    self.configTickResidYAuto.setMaximumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
    self.configTickResidYAuto.setMinimumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
    self.Layout_configTickResidY.addWidget(self.configTickResidYAuto)
        
    self.configTickResidYEntry = QLineEditClick()
    self.configTickResidYEntry.setMaximumSize(QtCore.QSize(scaledDPI(150), scaledDPI(BASE_SIZE)))
    self.configTickResidYEntry.setMinimumSize(QtCore.QSize(scaledDPI(150), scaledDPI(BASE_SIZE)))
    self.Layout_configTickResidY.addWidget(self.configTickResidYEntry)

    # tick mark config
    blah = self.HLine()
    self.vLayout.addWidget(blah)
    self.configTickMarkBox = {}; self.Layout_configTickMark = {}
    self.configTickMarkLabel = {}; self.configTickMarkCheck = {}
    self.configTickMarkWidthLabel = {}; self.configTickMarkWidth = {}
    self.configTickMarkLengthLabel = {}; self.configTickMarkLength = {}
    self.configTickMarkDirection = {}; self.configTickMarkColor = {}
    for axis in ['bottom', 'top', 'left', 'right']:
      self.configTickMarkBox[axis] = QWidgetMac()
      self.vLayout.addWidget(self.configTickMarkBox[axis])
      self.Layout_configTickMark[axis] = QtWidgets.QHBoxLayout(self.configTickMarkBox[axis])
      self.Layout_configTickMark[axis].setContentsMargins(0, 0, 0, 0)
      self.Layout_configTickMark[axis].setAlignment(QtCore.Qt.AlignLeft)
      self.configTickMarkLabel[axis] = QtWidgets.QLabel('tick_'+axis)
      self.configTickMarkLabel[axis].setText("<html><head/><body><span style=\"font-weight:bold;\">tick " + axis + "</span></body></html>")
      self.configTickMarkLabel[axis].setMaximumSize(QtCore.QSize(scaledDPI(61), scaledDPI(BASE_SIZE)))
      self.configTickMarkLabel[axis].setMinimumSize(QtCore.QSize(scaledDPI(61), scaledDPI(BASE_SIZE)))
      self.Layout_configTickMark[axis].addWidget(self.configTickMarkLabel[axis])

      self.configTickMarkCheck[axis] = QtWidgets.QCheckBox()
      self.configTickMarkCheck[axis].setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 8), scaledDPI(BASE_SIZE - 8)))
      self.Layout_configTickMark[axis].addWidget(self.configTickMarkCheck[axis])

      self.configTickMarkDirection[axis] = QComboBoxMac()
      self.directionstyles = ['in', 'out', 'inout']
      self.configTickMarkDirection[axis].setMinimumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      self.configTickMarkDirection[axis].setMaximumSize(QtCore.QSize(scaledDPI(45), scaledDPI(BASE_SIZE)))
      self.Layout_configTickMark[axis].addWidget(self.configTickMarkDirection[axis])

      self.configTickMarkColor[axis] = QPushButtonMac()
      self.configTickMarkColor[axis].setAutoFillBackground(False)
      self.configTickMarkColor[axis].setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.configTickMarkColor[axis].setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.configTickMarkColor[axis].setCursor(QtCore.Qt.PointingHandCursor)
      self.Layout_configTickMark[axis].addWidget(self.configTickMarkColor[axis])
  
      self.configTickMarkWidthLabel[axis] = QtWidgets.QLabel('width')
      self.configTickMarkWidthLabel[axis].setMinimumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
      self.configTickMarkWidthLabel[axis].setMaximumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
      self.Layout_configTickMark[axis].addWidget(self.configTickMarkWidthLabel[axis])
      self.configTickMarkWidth[axis] = QLineEditClick()
      self.configTickMarkWidth[axis].setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configTickMarkWidth[axis].setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configTickMarkWidth[axis].setValidator(self.validFloat)
      self.Layout_configTickMark[axis].addWidget(self.configTickMarkWidth[axis])

      self.configTickMarkLengthLabel[axis] = QtWidgets.QLabel('length')
      self.configTickMarkLengthLabel[axis].setMinimumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
      self.configTickMarkLengthLabel[axis].setMaximumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
      self.Layout_configTickMark[axis].addWidget(self.configTickMarkLengthLabel[axis])
      self.configTickMarkLength[axis] = QLineEditClick()
      self.configTickMarkLength[axis].setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configTickMarkLength[axis].setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configTickMarkLength[axis].setValidator(self.validFloat)
      self.Layout_configTickMark[axis].addWidget(self.configTickMarkLength[axis])

    # grid config
    blah = self.HLine()
    self.vLayout.addWidget(blah)
    self.configGridBox = {}; self.Layout_configGrid = {}
    self.configGridLabel = {}; self.configGridCheck = {}
    self.configGridWidthLabel = {}; self.configGridWidth = {}
    self.configGridColor = {}; self.configGridStyle = {}
    self.configGridDashStyle = {}; self.configGridOrder = {}
    for axis in ['x', 'y']:
      self.configGridBox[axis] = QWidgetMac()
      self.vLayout.addWidget(self.configGridBox[axis])
      self.Layout_configGrid[axis] = QtWidgets.QHBoxLayout(self.configGridBox[axis])
      self.Layout_configGrid[axis].setContentsMargins(0, 0, 0, 0)
      self.Layout_configGrid[axis].setAlignment(QtCore.Qt.AlignLeft)
      self.configGridLabel[axis] = QtWidgets.QLabel()
      self.configGridLabel[axis].setText("<html><head/><body><span style=\"font-weight:bold;\">grid " + axis + "</span></body></html>")
      self.configGridLabel[axis].setMaximumSize(QtCore.QSize(scaledDPI(34), scaledDPI(BASE_SIZE)))
      self.configGridLabel[axis].setMinimumSize(QtCore.QSize(scaledDPI(34), scaledDPI(BASE_SIZE)))
      self.Layout_configGrid[axis].addWidget(self.configGridLabel[axis])

      self.configGridCheck[axis] = QtWidgets.QCheckBox()
      self.configGridCheck[axis].setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 8), scaledDPI(BASE_SIZE - 8)))
      self.Layout_configGrid[axis].addWidget(self.configGridCheck[axis])

      self.orderstyles = ['front', 'back']
      self.configGridOrder[axis] = QComboBoxMac()
      self.configGridOrder[axis].setMinimumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.configGridOrder[axis].setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.Layout_configGrid[axis].addWidget(self.configGridOrder[axis])

      self.configGridColor[axis] = QPushButtonMac()
      self.configGridColor[axis].setAutoFillBackground(False)
      self.configGridColor[axis].setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.configGridColor[axis].setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.configGridColor[axis].setCursor(QtCore.Qt.PointingHandCursor)
      self.Layout_configGrid[axis].addWidget(self.configGridColor[axis])
  
      self.configGridWidthLabel[axis] = QtWidgets.QLabel('width')
      self.configGridWidthLabel[axis].setMinimumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
      self.configGridWidthLabel[axis].setMaximumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
      self.Layout_configGrid[axis].addWidget(self.configGridWidthLabel[axis])
      self.configGridWidth[axis] = QLineEditClick()
      self.configGridWidth[axis].setText(str(self.parent.plotArea.gridWidth[axis]))
      self.configGridWidth[axis].setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configGridWidth[axis].setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.configGridWidth[axis].setValidator(self.validFloat)
      self.Layout_configGrid[axis].addWidget(self.configGridWidth[axis])

      self.configGridStyle[axis] = QComboBoxMac()
      self.configGridStyle[axis].setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
      self.configGridStyle[axis].setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
      self.Layout_configGrid[axis].addWidget(self.configGridStyle[axis])

      self.configGridDashStyle[axis] = QComboBoxMac()
      self.configGridDashStyle[axis].setMinimumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
      self.configGridDashStyle[axis].setMaximumSize(QtCore.QSize(scaledDPI(70), scaledDPI(BASE_SIZE)))
      self.Layout_configGrid[axis].addWidget(self.configGridDashStyle[axis])

    # legend config
    self.placementstyles = 'best;upper right;upper left;lower left;lower right;right;center left;center right;lower center;upper center;center'.split(';')
    blah = self.HLine()
    self.vLayout.addWidget(blah)
    self.configLegendBox = QWidgetMac()
    self.vLayout.addWidget(self.configLegendBox)
    self.Layout_configLegend = QtWidgets.QHBoxLayout(self.configLegendBox)
    self.Layout_configLegend.setContentsMargins(0, 0, 0, 0)
    self.Layout_configLegend.setAlignment(QtCore.Qt.AlignLeft)
    
    self.configLegendLabel = QtWidgets.QLabel()
    self.configLegendLabel.setText("<html><head/><body><span style=\"font-weight:bold;\">legend</span></body></html>")
    self.configLegendLabel.setMaximumSize(QtCore.QSize(scaledDPI(34), scaledDPI(BASE_SIZE)))
    self.configLegendLabel.setMinimumSize(QtCore.QSize(scaledDPI(34), scaledDPI(BASE_SIZE)))
    self.Layout_configLegend.addWidget(self.configLegendLabel)
    self.configLegendCheck = QtWidgets.QCheckBox()
    self.configLegendCheck.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 8), scaledDPI(BASE_SIZE - 8)))
    self.Layout_configLegend.addWidget(self.configLegendCheck)

    self.configLegendPlacement = QComboBoxMac()
    self.configLegendPlacement.addItems(self.placementstyles)
    self.configLegendPlacement.setMaximumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
    self.configLegendPlacement.setMinimumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
    self.Layout_configLegend.addWidget(self.configLegendPlacement)

    self.configLegendColor = {}; self.configLegendColorLabel = {}
    for prop in ['face', 'edge']:
      self.configLegendColorLabel[prop] = QtWidgets.QLabel(prop)
      self.configLegendColorLabel[prop].setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
      self.Layout_configLegend.addWidget(self.configLegendColorLabel[prop])
      self.configLegendColor[prop] = QPushButtonMac()
      self.configLegendColor[prop].setAutoFillBackground(False)
      self.configLegendColor[prop].setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.configLegendColor[prop].setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
      self.configLegendColor[prop].setCursor(QtCore.Qt.PointingHandCursor)
      self.Layout_configLegend.addWidget(self.configLegendColor[prop])

    self.configLegendEdgeWidthLabel = QtWidgets.QLabel('width')
    self.configLegendEdgeWidthLabel.setMaximumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
    self.Layout_configLegend.addWidget(self.configLegendEdgeWidthLabel)
    self.configLegendEdgeWidth = QLineEditClick()
    self.configLegendEdgeWidth.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configLegendEdgeWidth.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configLegendEdgeWidth.setValidator(self.validFloat)
    self.Layout_configLegend.addWidget(self.configLegendEdgeWidth)
 
    self.configLegendShadowLabel = QtWidgets.QLabel('shadow')
    self.configLegendShadowLabel.setMaximumSize(QtCore.QSize(scaledDPI(50), scaledDPI(BASE_SIZE)))
    self.Layout_configLegend.addWidget(self.configLegendShadowLabel)
    self.configLegendShadowCheck = QtWidgets.QCheckBox()
    self.configLegendShadowCheck.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 8), scaledDPI(BASE_SIZE - 8)))
    self.Layout_configLegend.addWidget(self.configLegendShadowCheck)

    self.configLegendBox2 = QWidgetMac()
    self.vLayout.addWidget(self.configLegendBox2)
    self.Layout_configLegend2 = QtWidgets.QHBoxLayout(self.configLegendBox2)
    self.Layout_configLegend2.setContentsMargins(0, 0, 0, 0)
    self.Layout_configLegend2.setAlignment(QtCore.Qt.AlignLeft)

    spacer = QtWidgets.QLabel()
    spacer.setMaximumSize(QtCore.QSize(scaledDPI(4), scaledDPI(BASE_SIZE)))
    spacer.setMinimumSize(QtCore.QSize(scaledDPI(4), scaledDPI(BASE_SIZE)))
    self.Layout_configLegend2.addWidget(spacer)
    
    self.configLegendSizeLabel = QtWidgets.QLabel('font')
    self.configLegendSizeLabel.setMaximumSize(QtCore.QSize(scaledDPI(20), scaledDPI(BASE_SIZE)))
    self.Layout_configLegend2.addWidget(self.configLegendSizeLabel)
    self.configLegendLabelColor = QPushButtonMac()
    self.configLegendLabelColor.setAutoFillBackground(False)
    self.configLegendLabelColor.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configLegendLabelColor.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configLegendLabelColor.setCursor(QtCore.Qt.PointingHandCursor)
    self.Layout_configLegend2.addWidget(self.configLegendLabelColor)

    self.configLegendLabelSize = QLineEditClick()
    self.configLegendLabelSize.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configLegendLabelSize.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configLegendLabelSize.setValidator(self.validFloat)
    self.Layout_configLegend2.addWidget(self.configLegendLabelSize)

    self.configLegendLabelFont = QComboBoxMac()
    self.configLegendLabelFont.addItems(self.parent.fontNames)
    self.configLegendLabelFont.setMaximumSize(QtCore.QSize(scaledDPI(150), scaledDPI(BASE_SIZE)))
    self.configLegendLabelFont.setMinimumSize(QtCore.QSize(scaledDPI(150), scaledDPI(BASE_SIZE)))
    self.Layout_configLegend2.addWidget(self.configLegendLabelFont)

    # canvas config
    blah = self.HLine()
    self.vLayout.addWidget(blah)
    self.configCanvasBox = QWidgetMac()
    self.vLayout.addWidget(self.configCanvasBox)
    self.Layout_configCanvas = QtWidgets.QHBoxLayout(self.configCanvasBox)
    self.Layout_configCanvas.setContentsMargins(0, 0, 0, 0)
    self.Layout_configCanvas.setAlignment(QtCore.Qt.AlignLeft)
    
    self.configFigureLabel = QtWidgets.QLabel()
    self.configFigureLabel.setText("<html><head/><body><span style=\"font-weight:bold;\">figure</span></body></html>")
    self.configFigureLabel.setMaximumSize(QtCore.QSize(scaledDPI(34), scaledDPI(BASE_SIZE)))
    self.configFigureLabel.setMinimumSize(QtCore.QSize(scaledDPI(34), scaledDPI(BASE_SIZE)))
    self.Layout_configCanvas.addWidget(self.configFigureLabel)
    self.configFigureColorButton = QPushButtonMac()
    self.configFigureColorButton.setAutoFillBackground(False)
    self.configFigureColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configFigureColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configFigureColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.Layout_configCanvas.addWidget(self.configFigureColorButton)

    self.configCanvasLabel = QtWidgets.QLabel('canvas')
    self.configCanvasLabel.setMinimumSize(QtCore.QSize(scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.configCanvasLabel.setMaximumSize(QtCore.QSize(scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.Layout_configCanvas.addWidget(self.configCanvasLabel)
    self.configCanvasColorButton = QPushButtonMac()
    self.configCanvasColorButton.setAutoFillBackground(False)
    self.configCanvasColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configCanvasColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configCanvasColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.Layout_configCanvas.addWidget(self.configCanvasColorButton)

    # canvas dimensions
    self.exportSizeBox = QWidgetMac()
    self.vLayout.addWidget(self.exportSizeBox)
    self.Layout_exportSize = QtWidgets.QHBoxLayout(self.exportSizeBox)
    self.Layout_exportSize.setContentsMargins(0, 0, 0, 0)
    self.Layout_exportSize.setAlignment(QtCore.Qt.AlignLeft)

    spacer = QtWidgets.QLabel()
    spacer.setMaximumSize(QtCore.QSize(scaledDPI(4), scaledDPI(BASE_SIZE)))
    spacer.setMinimumSize(QtCore.QSize(scaledDPI(4), scaledDPI(BASE_SIZE)))
    self.Layout_exportSize.addWidget(spacer)
    
    self.exportSizeBaseLabel = QtWidgets.QLabel('fig.')
    self.exportSizeBaseLabel.setMaximumSize(QtCore.QSize(scaledDPI(18), scaledDPI(BASE_SIZE)))
    self.exportSizeBaseLabel.setMinimumSize(QtCore.QSize(scaledDPI(18), scaledDPI(BASE_SIZE)))
    self.Layout_exportSize.addWidget(self.exportSizeBaseLabel)
    self.exportSizeXLabel = QtWidgets.QLabel('width')
    self.exportSizeXLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.exportSizeXLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.Layout_exportSize.addWidget(self.exportSizeXLabel)
    self.exportSizeX = QLineEditClick()
    self.exportSizeX.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.exportSizeX.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.exportSizeX.setValidator(self.validFloat)
    self.Layout_exportSize.addWidget(self.exportSizeX)
    self.exportSizeYLabel = QtWidgets.QLabel('height')
    self.exportSizeYLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.exportSizeYLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.Layout_exportSize.addWidget(self.exportSizeYLabel)
    self.exportSizeY = QLineEditClick()
    self.exportSizeY.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.exportSizeY.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.exportSizeY.setValidator(self.validFloat)
    self.Layout_exportSize.addWidget(self.exportSizeY)
    self.exportSizeCurrentButton = QPushButtonMac()
    self.exportSizeCurrentButton.setText('Use screen')
    self.exportSizeCurrentButton.setMaximumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
    self.exportSizeCurrentButton.setMinimumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
    self.Layout_exportSize.addWidget(self.exportSizeCurrentButton)
    
    # pad graphics
    self.exportPadBox = QWidgetMac()
    self.vLayout.addWidget(self.exportPadBox)
    self.Layout_exportPad = QtWidgets.QHBoxLayout(self.exportPadBox)
    self.Layout_exportPad.setContentsMargins(0, 0, 0, 0)
    self.Layout_exportPad.setAlignment(QtCore.Qt.AlignLeft)

    spacer = QtWidgets.QLabel()
    spacer.setMaximumSize(QtCore.QSize(scaledDPI(4), scaledDPI(BASE_SIZE)))
    spacer.setMinimumSize(QtCore.QSize(scaledDPI(4), scaledDPI(BASE_SIZE)))
    self.Layout_exportPad.addWidget(spacer)

    self.exportPadLabelMain = QtWidgets.QLabel('pad')
    self.exportPadLabelMain.setMaximumSize(QtCore.QSize(scaledDPI(18), scaledDPI(BASE_SIZE)))
    self.exportPadLabelMain.setMinimumSize(QtCore.QSize(scaledDPI(18), scaledDPI(BASE_SIZE)))
    self.Layout_exportPad.addWidget(self.exportPadLabelMain)

    self.exportPadLabel = {}; self.exportPadEntry = {}
    for axis in ['bottom', 'top', 'left', 'right']:
      self.exportPadLabel[axis] = QtWidgets.QLabel(axis)
      self.exportPadLabel[axis].setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.exportPadLabel[axis].setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
      self.Layout_exportPad.addWidget(self.exportPadLabel[axis])

      self.exportPadEntry[axis] = QLineEditClick()
      self.exportPadEntry[axis].setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.exportPadEntry[axis].setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
      self.exportPadEntry[axis].setValidator(self.validFloat)
      self.Layout_exportPad.addWidget(self.exportPadEntry[axis])
    
    # xkcdify
    blah = self.HLine()
    self.vLayout.addWidget(blah)
    self.configXkcdBox = QWidgetMac()
    self.vLayout.addWidget(self.configXkcdBox)
    self.Layout_configXkcd = QtWidgets.QHBoxLayout(self.configXkcdBox)
    self.Layout_configXkcd.setContentsMargins(0, 0, 0, 0)
    self.Layout_configXkcd.setAlignment(QtCore.Qt.AlignLeft)
    
    self.configXkcdLabel = QtWidgets.QLabel()
    self.configXkcdLabel.setText("<html><head/><body><span style=\"font-weight:bold;\">xkcdify</span></body></html>")
    self.configXkcdLabel.setMaximumSize(QtCore.QSize(scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.configXkcdLabel.setMinimumSize(QtCore.QSize(scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.Layout_configXkcd.addWidget(self.configXkcdLabel)
    self.configXkcdCheck = QtWidgets.QCheckBox()
    self.configXkcdCheck.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 8), scaledDPI(BASE_SIZE - 8)))
    self.Layout_configXkcd.addWidget(self.configXkcdCheck)

    self.xkcdScaleLabel = QtWidgets.QLabel('scale')
    self.xkcdScaleLabel.setMaximumSize(QtCore.QSize(scaledDPI(25), scaledDPI(BASE_SIZE)))
    self.xkcdScaleLabel.setMinimumSize(QtCore.QSize(scaledDPI(25), scaledDPI(BASE_SIZE)))
    self.Layout_configXkcd.addWidget(self.xkcdScaleLabel)
    self.xkcdScale = QLineEditClick()
    self.xkcdScale.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.xkcdScale.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.xkcdScale.setValidator(self.validFloat)
    self.Layout_configXkcd.addWidget(self.xkcdScale)

    self.xkcdLengthLabel = QtWidgets.QLabel('length')
    self.xkcdLengthLabel.setMaximumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.xkcdLengthLabel.setMinimumSize(QtCore.QSize(scaledDPI(33), scaledDPI(BASE_SIZE)))
    self.Layout_configXkcd.addWidget(self.xkcdLengthLabel)
    self.xkcdLength = QLineEditClick()
    self.xkcdLength.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.xkcdLength.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.xkcdLength.setValidator(self.validFloat)
    self.Layout_configXkcd.addWidget(self.xkcdLength)

    self.xkcdRandomLabel = QtWidgets.QLabel('random')
    self.xkcdRandomLabel.setMaximumSize(QtCore.QSize(scaledDPI(36), scaledDPI(BASE_SIZE)))
    self.xkcdRandomLabel.setMinimumSize(QtCore.QSize(scaledDPI(36), scaledDPI(BASE_SIZE)))
    self.Layout_configXkcd.addWidget(self.xkcdRandomLabel)
    self.xkcdRandom = QLineEditClick()
    self.xkcdRandom.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.xkcdRandom.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.xkcdRandom.setValidator(self.validFloat)
    self.Layout_configXkcd.addWidget(self.xkcdRandom)

    # path effects -- stroke
    self.configPathEffectsBox = QWidgetMac()
    self.vLayout.addWidget(self.configPathEffectsBox)
    self.Layout_configPathEffects = QtWidgets.QHBoxLayout(self.configPathEffectsBox)
    self.Layout_configPathEffects.setContentsMargins(0, 0, 0, 0)
    self.Layout_configPathEffects.setAlignment(QtCore.Qt.AlignLeft)
    
    self.configPathEffectsLabel = QtWidgets.QLabel()
    self.configPathEffectsLabel.setText("<html><head/><body><span style=\"font-weight:bold;\">outline</span></body></html>")
    self.configPathEffectsLabel.setMaximumSize(QtCore.QSize(scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.configPathEffectsLabel.setMinimumSize(QtCore.QSize(scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.Layout_configPathEffects.addWidget(self.configPathEffectsLabel)
    self.configPathEffectsCheck = QtWidgets.QCheckBox()
    self.configPathEffectsCheck.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 8), scaledDPI(BASE_SIZE - 8)))
    self.Layout_configPathEffects.addWidget(self.configPathEffectsCheck)

    self.configPathEffectsColorButton = QPushButtonMac()
    self.configPathEffectsColorButton.setAutoFillBackground(False)
    self.configPathEffectsColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configPathEffectsColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configPathEffectsColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.Layout_configPathEffects.addWidget(self.configPathEffectsColorButton)

    self.configPathEffectsWidthLabel = QtWidgets.QLabel('width')
    self.configPathEffectsWidthLabel.setMinimumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
    self.configPathEffectsWidthLabel.setMaximumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
    self.Layout_configPathEffects.addWidget(self.configPathEffectsWidthLabel)
    self.configPathEffectsWidth = QLineEditClick()
    self.configPathEffectsWidth.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configPathEffectsWidth.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configPathEffectsWidth.setValidator(self.validFloat)
    self.Layout_configPathEffects.addWidget(self.configPathEffectsWidth)
 
    # path effects -- shadow
    self.configPathShadowBox = QWidgetMac()
    self.vLayout.addWidget(self.configPathShadowBox)
    self.Layout_configPathShadow = QtWidgets.QHBoxLayout(self.configPathShadowBox)
    self.Layout_configPathShadow.setContentsMargins(0, 0, 0, 0)
    self.Layout_configPathShadow.setAlignment(QtCore.Qt.AlignLeft)
    
    self.configPathShadowLabel = QtWidgets.QLabel()
    self.configPathShadowLabel.setText("<html><head/><body><span style=\"font-weight:bold;\">shadow</span></body></html>")
    self.configPathShadowLabel.setMaximumSize(QtCore.QSize(scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.configPathShadowLabel.setMinimumSize(QtCore.QSize(scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.Layout_configPathShadow.addWidget(self.configPathShadowLabel)
    self.configPathShadowCheck = QtWidgets.QCheckBox()
    self.configPathShadowCheck.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 8), scaledDPI(BASE_SIZE - 8)))
    self.Layout_configPathShadow.addWidget(self.configPathShadowCheck)

    self.configPathShadowColorButton = QPushButtonMac()
    self.configPathShadowColorButton.setAutoFillBackground(False)
    self.configPathShadowColorButton.setMaximumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configPathShadowColorButton.setMinimumSize(QtCore.QSize(scaledDPI(BASE_SIZE - 2), scaledDPI(BASE_SIZE - 2)))
    self.configPathShadowColorButton.setCursor(QtCore.Qt.PointingHandCursor)
    self.Layout_configPathShadow.addWidget(self.configPathShadowColorButton)

    self.configPathShadowOffXLabel = QtWidgets.QLabel('offX')
    self.configPathShadowOffXLabel.setMinimumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
    self.configPathShadowOffXLabel.setMaximumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
    self.Layout_configPathShadow.addWidget(self.configPathShadowOffXLabel)
    self.configPathShadowOffX = QLineEditClick()
    self.configPathShadowOffX.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configPathShadowOffX.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configPathShadowOffX.setValidator(self.validFloat)
    self.Layout_configPathShadow.addWidget(self.configPathShadowOffX)
 
    self.configPathShadowOffYLabel = QtWidgets.QLabel('offY')
    self.configPathShadowOffYLabel.setMinimumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
    self.configPathShadowOffYLabel.setMaximumSize(QtCore.QSize(scaledDPI(30), scaledDPI(BASE_SIZE)))
    self.Layout_configPathShadow.addWidget(self.configPathShadowOffYLabel)
    self.configPathShadowOffY = QLineEditClick()
    self.configPathShadowOffY.setMaximumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configPathShadowOffY.setMinimumSize(QtCore.QSize(scaledDPI(32), scaledDPI(BASE_SIZE)))
    self.configPathShadowOffY.setValidator(self.validFloat)
    self.Layout_configPathShadow.addWidget(self.configPathShadowOffY)
    
    self.vLayout.addStretch()
 
    # export graphics
    self.exportBox = QWidgetMac()
    self.vLayout_0.addWidget(self.exportBox)
    self.Layout_export = QtWidgets.QHBoxLayout(self.exportBox)
    self.Layout_export.setContentsMargins(0, 0, 0, 0)
    self.Layout_export.setAlignment(QtCore.Qt.AlignLeft)
    self.previewButton = QPushButtonMac()
    self.previewButton.setText('Preview')
    self.previewButton.setMaximumSize(QtCore.QSize(scaledDPI(100), scaledDPI(BASE_SIZE)))
    self.previewButton.setMinimumSize(QtCore.QSize(scaledDPI(100), scaledDPI(BASE_SIZE)))
    self.Layout_export.addWidget(self.previewButton)
    self.exportButton = QPushButtonMac()
    self.exportButton.setText('Export graphics')
    self.exportButton.setMaximumSize(QtCore.QSize(scaledDPI(100), scaledDPI(BASE_SIZE)))
    self.exportButton.setMinimumSize(QtCore.QSize(scaledDPI(100), scaledDPI(BASE_SIZE)))
    self.Layout_export.addWidget(self.exportButton)

    # load/save style
    self.loadStyleSet = QPushButtonMac()
    self.loadStyleSet.setText('Open style')
    self.loadStyleSet.setMaximumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
    self.loadStyleSet.setMinimumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
    self.Layout_export.addWidget(self.loadStyleSet)
    self.saveStyleSet = QPushButtonMac()
    self.saveStyleSet.setText('Save style')
    self.saveStyleSet.setMaximumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
    self.saveStyleSet.setMinimumSize(QtCore.QSize(scaledDPI(80), scaledDPI(BASE_SIZE)))
    self.Layout_export.addWidget(self.saveStyleSet)

  def updateFields(self, initialize=False):
    # updates all fields in entry mask
    defaultFont = 'DejaVu Sans'
    # x label config
    self.configXName.setText(self.parent.plotArea.labelX)
    colorvalue = [int(i*255.0) for i in self.parent.plotArea.labelXColor[0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.configXColorButton.setStyleSheet(colorstr)
    self.configXSize.setText(str(self.parent.plotArea.labelXSize))
    if(self.parent.plotArea.axisFont['x'] in self.parent.fontNames):
      currindex = self.parent.fontNames.index(self.parent.plotArea.axisFont['x'])
      self.configXFont.setCurrentIndex(currindex)
    elif(defaultFont in self.parent.fontNames):
      currindex = self.parent.fontNames.index(defaultFont)
      self.configXFont.setCurrentIndex(currindex)
      self.parent.plotArea.axisFont['x'] = defaultFont
    else:
      self.configXFont.setCurrentIndex(0)
    if(self.parent.plotArea.labelXAlignment in self.alignHorizontal):
      currindex = self.alignHorizontal.index(self.parent.plotArea.labelXAlignment)
      self.configXAlignment.setCurrentIndex(currindex)
    else:
      self.configXAlignment.setCurrentIndex(0)
    self.configXPad.setText(str(self.parent.plotArea.labelXPad))
    self.configXPos.setText(str(self.parent.plotArea.labelXPos))
    self.configXAngle.setText(str(self.parent.plotArea.labelXAngle))

    # y label config
    self.configYName.setText(self.parent.plotArea.labelY)
    colorvalue = [int(i*255.0) for i in self.parent.plotArea.labelYColor[0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.configYColorButton.setStyleSheet(colorstr)
    self.configYSize.setText(str(self.parent.plotArea.labelYSize))
    if(self.parent.plotArea.axisFont['y'] in self.parent.fontNames):
      currindex = self.parent.fontNames.index(self.parent.plotArea.axisFont['y'])
      self.configYFont.setCurrentIndex(currindex)
    elif(defaultFont in self.parent.fontNames):
      currindex = self.parent.fontNames.index(defaultFont)
      self.configYFont.setCurrentIndex(currindex)
      self.parent.plotArea.axisFont['y'] = defaultFont
    else:
      self.configYFont.setCurrentIndex(0)
    if(self.parent.plotArea.labelYAlignment in self.alignVertical):
      currindex = self.alignVertical.index(self.parent.plotArea.labelYAlignment)
      self.configYAlignment.setCurrentIndex(currindex)
    else:
      self.configYAlignment.setCurrentIndex(0)
    self.configYPad.setText(str(self.parent.plotArea.labelYPad))
    self.configYPos.setText(str(self.parent.plotArea.labelYPos))
    self.configYAngle.setText(str(self.parent.plotArea.labelYAngle))

    # axis config
    for axis in ['bottom', 'top', 'left', 'right']:
      self.configAxisCheck[axis].blockSignals(True)
      self.configAxisCheck[axis].setChecked(self.parent.plotArea.axisVisible[axis])
      self.configAxisCheck[axis].blockSignals(False)
      colorvalue = [int(i*255.0) for i in self.parent.plotArea.axisColor[axis][0:3]]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.configAxisColor[axis].setStyleSheet(colorstr)
      self.configAxisWidth[axis].setText(str(self.parent.plotArea.axisWidth[axis]))
      if(initialize):
        for entry in self.linestyles:
          self.configAxisStyle[axis].addItem(entry)
      if(self.parent.plotArea.axisStyle[axis] in self.linestyles):
        currindex = self.linestyles.index(self.parent.plotArea.axisStyle[axis])
        self.configAxisStyle[axis].setCurrentIndex(currindex)
      else:
        self.configAxisStyle[axis].setCurrentIndex(0)
      if(initialize):
        for entry in self.dashstyles:
          self.configAxisDashStyle[axis].addItem(entry)
      if(self.parent.plotArea.axisDashStyle[axis] in self.dashstyles):
        currindex = self.dashstyles.index(self.parent.plotArea.axisDashStyle[axis])
        self.configAxisDashStyle[axis].setCurrentIndex(currindex)
      else:
        self.configAxisDashStyle[axis].setCurrentIndex(0)
        
    # arrow config
    for axis in ['x', 'y']:
      self.configArrowCheck[axis].blockSignals(True)
      self.configArrowCheck[axis].setChecked(self.parent.plotArea.arrowVisible[axis])
      self.configArrowCheck[axis].blockSignals(False)
      colorvalue = [int(i*255.0) for i in self.parent.plotArea.arrowColor[axis][0:3]]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.configArrowLineColor[axis].setStyleSheet(colorstr)
      colorvalue = [int(i*255.0) for i in self.parent.plotArea.arrowFill[axis][0:3]]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.configArrowFillColor[axis].setStyleSheet(colorstr)
      self.configArrowHeadLength[axis].setText(str(self.parent.plotArea.arrowHeadLength[axis]))
      self.configArrowHeadWidth[axis].setText(str(self.parent.plotArea.arrowHeadWidth[axis]))
      self.configArrowOverhang[axis].setText(str(self.parent.plotArea.arrowOverhang[axis]))
      self.configArrowOffset[axis].setText(str(self.parent.plotArea.arrowOffset[axis]))

    # x ticks config
    tickstr = ', '.join([str(i) for i in self.parent.plotArea.ticksX])
    self.configTickXEntry.setText(tickstr)
    colorvalue = [int(i*255.0) for i in self.parent.plotArea.ticksXColor[0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.configTickXColorButton.setStyleSheet(colorstr)
    self.configTickXSize.setText(str(self.parent.plotArea.ticksXSize))
    self.configTickXAngle.setText(str(self.parent.plotArea.ticksXAngle))
    if(self.parent.plotArea.tickFont['x'] in self.parent.fontNames):
      currindex = self.parent.fontNames.index(self.parent.plotArea.tickFont['x'])
      self.configTickXFont.setCurrentIndex(currindex)
    elif(defaultFont in self.parent.fontNames):
      currindex = self.parent.fontNames.index(defaultFont)
      self.configTickXFont.setCurrentIndex(currindex)
      self.parent.plotArea.tickFont['x'] = defaultFont
    else:
      self.configTickXFont.setCurrentIndex(0)

    # y ticks config
    tickstr = ', '.join([str(i) for i in self.parent.plotArea.ticksY])
    self.configTickYEntry.setText(tickstr)
    colorvalue = [int(i*255.0) for i in self.parent.plotArea.ticksYColor[0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.configTickYColorButton.setStyleSheet(colorstr)
    self.configTickYSize.setText(str(self.parent.plotArea.ticksYSize))
    self.configTickYAngle.setText(str(self.parent.plotArea.ticksYAngle))
    if(self.parent.plotArea.tickFont['y'] in self.parent.fontNames):
      currindex = self.parent.fontNames.index(self.parent.plotArea.tickFont['y'])
      self.configTickYFont.setCurrentIndex(currindex)
    elif(defaultFont in self.parent.fontNames):
      currindex = self.parent.fontNames.index(defaultFont)
      self.configTickYFont.setCurrentIndex(currindex)
      self.parent.plotArea.tickFont['y'] = defaultFont
    else:
      self.configTickYFont.setCurrentIndex(0)

    # y resid ticks config
    tickstr = ', '.join([str(i) for i in self.parent.plotArea.ticksResidY])
    self.configTickResidYEntry.setText(tickstr)

    # tick mark config
    for axis in ['bottom', 'top', 'left', 'right']:
      self.configTickMarkCheck[axis].blockSignals(True)
      self.configTickMarkCheck[axis].setChecked(self.parent.plotArea.ticksVisible[axis])
      self.configTickMarkCheck[axis].blockSignals(False)
      if(initialize):
        for entry in self.directionstyles:
          self.configTickMarkDirection[axis].addItem(entry)
      if(self.parent.plotArea.ticksDirection[axis] in self.directionstyles):
        currindex = self.directionstyles.index(self.parent.plotArea.ticksDirection[axis])
        self.configTickMarkDirection[axis].setCurrentIndex(currindex)
      else:
        self.configTickMarkDirection[axis].setCurrentIndex(0)
      colorvalue = [int(i*255.0) for i in self.parent.plotArea.ticksColor[axis][0:3]]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.configTickMarkColor[axis].setStyleSheet(colorstr)
      self.configTickMarkWidth[axis].setText(str(self.parent.plotArea.ticksWidth[axis]))
      self.configTickMarkLength[axis].setText(str(self.parent.plotArea.ticksLength[axis]))
        
    # grid config
    for axis in ['x', 'y']:
      self.configGridCheck[axis].blockSignals(True)
      self.configGridCheck[axis].setChecked(self.parent.plotArea.gridVisible[axis])
      self.configGridCheck[axis].blockSignals(False)
      colorvalue = [int(i*255.0) for i in self.parent.plotArea.gridColor[axis][0:3]]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.configGridColor[axis].setStyleSheet(colorstr)
      self.configGridWidth[axis].setText(str(self.parent.plotArea.gridWidth[axis]))
      if(initialize):
        for entry in self.linestyles:
          self.configGridStyle[axis].addItem(entry)
      if(self.parent.plotArea.gridStyle[axis] in self.linestyles):
        currindex = self.linestyles.index(self.parent.plotArea.gridStyle[axis])
        self.configGridStyle[axis].setCurrentIndex(currindex)
      else:
        self.configGridStyle[axis].setCurrentIndex(0)
      if(initialize):
        for entry in self.dashstyles:
          self.configGridDashStyle[axis].addItem(entry)
      if(self.parent.plotArea.gridDashStyle[axis] in self.dashstyles):
        currindex = self.dashstyles.index(self.parent.plotArea.gridDashStyle[axis])
        self.configGridDashStyle[axis].setCurrentIndex(currindex)
      else:
        self.configGridDashStyle[axis].setCurrentIndex(0)
      if(initialize):
        for entry in self.orderstyles:
          self.configGridOrder[axis].addItem(entry)
      if(self.parent.plotArea.gridOrder[axis] in self.orderstyles):
        currindex = self.orderstyles.index(self.parent.plotArea.gridOrder[axis])
        self.configGridOrder[axis].setCurrentIndex(currindex)
      else:
        self.configGridOrder[axis].setCurrentIndex(0)

    # legend config
    self.configLegendCheck.blockSignals(True)
    self.configLegendCheck.setChecked(self.parent.plotArea.legendVisible)
    self.configLegendCheck.blockSignals(False)
    if(self.parent.plotArea.legendPlacement in self.placementstyles):
      currindex = self.placementstyles.index(self.parent.plotArea.legendPlacement)
      self.configLegendPlacement.setCurrentIndex(currindex)
    else:
      self.configLegendPlacement.setCurrentIndex(0)
    for prop in ['face', 'edge']:
      colorvalue = [int(i*255.0) for i in self.parent.plotArea.legendColor[prop]]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.configLegendColor[prop].setStyleSheet(colorstr)
    self.configLegendEdgeWidth.setText(str(self.parent.plotArea.legendEdgeWidth))
    self.configLegendShadowCheck.blockSignals(True)
    self.configLegendShadowCheck.setChecked(self.parent.plotArea.legendShadow)
    self.configLegendShadowCheck.blockSignals(False)
    colorvalue = [int(i*255.0) for i in self.parent.plotArea.legendLabelColor]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.configLegendLabelColor.setStyleSheet(colorstr)
    self.configLegendLabelSize.setText(str(self.parent.plotArea.legendLabelSize))
    if(self.parent.plotArea.legendLabelFont in self.parent.fontNames):
      currindex = self.parent.fontNames.index(self.parent.plotArea.legendLabelFont)
      self.configLegendLabelFont.setCurrentIndex(currindex)
    elif(defaultFont in self.parent.fontNames):
      currindex = self.parent.fontNames.index(defaultFont)
      self.configLegendLabelFont.setCurrentIndex(currindex)
      self.parent.plotArea.legendLabelFont = defaultFont
    else:
      self.configLegendLabelFont.setCurrentIndex(0)
    
    # canvas config
    colorvalue = [int(i*255.0) for i in self.parent.plotArea.figureColor[0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.configFigureColorButton.setStyleSheet(colorstr)
    colorvalue = [int(i*255.0) for i in self.parent.plotArea.canvasColor[0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.configCanvasColorButton.setStyleSheet(colorstr)
    
    # canvas dimensions
    self.exportSizeX.setText(str(self.parent.plotArea.exportWidth))
    self.exportSizeY.setText(str(self.parent.plotArea.exportHeight))
    
    # pad graphics
    for axis in ['bottom', 'top', 'left', 'right']:
      self.exportPadEntry[axis].setText(str(self.parent.plotArea.padSize[axis]))

    # xkcd
    self.configXkcdCheck.blockSignals(True)
    self.configXkcdCheck.setChecked(self.parent.plotArea.xkcd)
    self.configXkcdCheck.blockSignals(False)
    self.xkcdScale.setText(str(self.parent.plotArea.xkcdScale))
    self.xkcdLength.setText(str(self.parent.plotArea.xkcdLength))
    self.xkcdRandom.setText(str(self.parent.plotArea.xkcdRandomness))
    
    # path effects
    self.configPathEffectsCheck.blockSignals(True)
    self.configPathEffectsCheck.setChecked(self.parent.plotArea.applyPathStroke)
    self.configPathEffectsCheck.blockSignals(False)
    colorvalue = [int(i*255.0) for i in self.parent.plotArea.pathStrokeColor[0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.configPathEffectsColorButton.setStyleSheet(colorstr)
    self.configPathEffectsWidth.setText(str(self.parent.plotArea.pathStrokeWidth))

    self.configPathShadowCheck.blockSignals(True)
    self.configPathShadowCheck.setChecked(self.parent.plotArea.applyPathShadow)
    self.configPathShadowCheck.blockSignals(False)
    colorvalue = [int(i*255.0) for i in self.parent.plotArea.pathShadowColor[0:3]]
    colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
    self.configPathShadowColorButton.setStyleSheet(colorstr)
    self.configPathShadowOffX.setText(str(self.parent.plotArea.pathShadowX))
    self.configPathShadowOffY.setText(str(self.parent.plotArea.pathShadowY))
  
  def connectEvents(self):
    # connects all events in entry mask
    # x label config
    self.configXName.editingFinished.connect(partial(self.changeAxisLabel, 'x'))
    self.configXColorButton.clicked.connect(partial(self.changeAxisLabelColor, axis = 'x'))
    self.configXSize.editingFinished.connect(partial(self.changeAxisLabelSize, entryfield = self.configXSize, axis = 'x', minval = 0.0, maxval = 100.0))
    self.configXFont.activated.connect(partial(self.setAxisFont, axis = 'x'))
    self.configXAlignment.activated.connect(partial(self.setAxisLabelAlignment, axis = 'x'))
    self.configXPad.editingFinished.connect(partial(self.changeAxisLabelPad, entryfield = self.configXPad, axis = 'x', minval = -100.0, maxval = 100.0))
    self.configXPos.editingFinished.connect(partial(self.changeAxisLabelPos, entryfield = self.configXPos, axis = 'x', minval = -0.5, maxval = 1.5))
    self.configXAngle.editingFinished.connect(partial(self.changeAxisLabelAngle, entryfield = self.configXAngle, axis = 'x', minval = 0.0, maxval = 360.0))
    
    # y label config
    self.configYName.editingFinished.connect(partial(self.changeAxisLabel, 'y'))
    self.configYColorButton.clicked.connect(partial(self.changeAxisLabelColor, axis = 'y'))
    self.configYSize.editingFinished.connect(partial(self.changeAxisLabelSize, entryfield = self.configYSize, axis = 'y', minval = 0.0, maxval = 100.0))
    self.configYFont.activated.connect(partial(self.setAxisFont, axis = 'y'))
    self.configYAlignment.activated.connect(partial(self.setAxisLabelAlignment, axis = 'y'))
    self.configYPad.editingFinished.connect(partial(self.changeAxisLabelPad, entryfield = self.configYPad, axis = 'y', minval = -100.0, maxval = 100.0))
    self.configYPos.editingFinished.connect(partial(self.changeAxisLabelPos, entryfield = self.configYPos, axis = 'y', minval = -0.5, maxval = 1.5))
    self.configYAngle.editingFinished.connect(partial(self.changeAxisLabelAngle, entryfield = self.configYAngle, axis = 'y', minval = 0.0, maxval = 360.0))

    # axis config
    for axis in ['bottom', 'top', 'left', 'right']:
      self.configAxisCheck[axis].stateChanged.connect(partial(self.setAxisVisibility, axis = axis))
      self.configAxisColor[axis].clicked.connect(partial(self.changeAxisColor, axis = axis))
      self.configAxisWidth[axis].editingFinished.connect(partial(self.changeAxisWidth, axis = axis, minval = 0.0, maxval = 100.0))
      self.configAxisStyle[axis].activated.connect(partial(self.setAxisStyle, axis = axis))
      self.configAxisDashStyle[axis].activated.connect(partial(self.setAxisDashStyle, axis = axis))

    # arrow config
    for axis in ['x', 'y']:
      self.configArrowCheck[axis].stateChanged.connect(partial(self.setAxisArrow, axis = axis))
      self.configArrowLineColor[axis].clicked.connect(partial(self.changeArrowColor, axis = axis, item='line'))
      self.configArrowFillColor[axis].clicked.connect(partial(self.changeArrowColor, axis = axis, item='fill'))
      self.configArrowHeadWidth[axis].editingFinished.connect(partial(self.changeArrowHeadWidth, axis = axis, minval = 0.0, maxval = 1.0))
      self.configArrowHeadLength[axis].editingFinished.connect(partial(self.changeArrowHeadLength, axis = axis, minval = 0.0, maxval = 1.0))
      self.configArrowOverhang[axis].editingFinished.connect(partial(self.changeArrowOverhang, axis = axis, minval = -1.0, maxval = 1.0))
      self.configArrowOffset[axis].editingFinished.connect(partial(self.changeArrowOffset, axis = axis, minval = 0.0, maxval = 1.0))

    # x ticks config
    self.configTickXAuto.clicked.connect(partial(self.automaticAxisTicks, axis = 'x'))
    self.configTickXEntry.editingFinished.connect(partial(self.changeAxisTicks, 'x'))
    self.configTickUseData.clicked.connect(self.dataAxisTicks)
    self.configTickXColorButton.clicked.connect(partial(self.changeTickLabelColor, axis = 'x'))
    self.configTickXSize.editingFinished.connect(partial(self.changeTickLabelSize, entryfield = self.configTickXSize, axis = 'x', minval = 0.0, maxval = 100.0))
    self.configTickXAngle.editingFinished.connect(partial(self.changeTickLabelAngle, entryfield = self.configTickXAngle, axis = 'x', minval = 0.0, maxval = 360.0))
    self.configTickXFont.activated.connect(partial(self.setTickFont, axis = 'x'))

    # y ticks config
    self.configTickYAuto.clicked.connect(partial(self.automaticAxisTicks, axis = 'y'))
    self.configTickYEntry.editingFinished.connect(partial(self.changeAxisTicks, 'y'))
    self.configTickYColorButton.clicked.connect(partial(self.changeTickLabelColor, axis = 'y'))
    self.configTickYSize.editingFinished.connect(partial(self.changeTickLabelSize, entryfield = self.configTickYSize, axis = 'y', minval = 0.0, maxval = 100.0))
    self.configTickYAngle.editingFinished.connect(partial(self.changeTickLabelAngle, entryfield = self.configTickYAngle, axis = 'y', minval = 0.0, maxval = 360.0))
    self.configTickYFont.activated.connect(partial(self.setTickFont, axis = 'y'))

    self.configTickResidYAuto.clicked.connect(partial(self.automaticAxisTicks, axis = 'resid'))
    self.configTickResidYEntry.editingFinished.connect(partial(self.changeAxisTicks, 'resid'))
    
    # tick mark config
    for axis in ['bottom', 'top', 'left', 'right']:
      self.configTickMarkCheck[axis].stateChanged.connect(partial(self.setTicksVisibility, axis = axis))
      self.configTickMarkDirection[axis].activated.connect(partial(self.setTickMarkDirection, axis = axis))
      self.configTickMarkColor[axis].clicked.connect(partial(self.changeTickMarkColor, axis = axis))
      self.configTickMarkWidth[axis].editingFinished.connect(partial(self.changeTickMarkWidth, axis = axis, minval = 0.0, maxval = 100.0))
      self.configTickMarkLength[axis].editingFinished.connect(partial(self.changeTickMarkLength, axis = axis, minval = 0.0, maxval = 100.0))

    # grid config
    for axis in ['x', 'y']:
      self.configGridCheck[axis].stateChanged.connect(partial(self.setGridVisibility, axis = axis))
      self.configGridColor[axis].clicked.connect(partial(self.changeGridColor, axis = axis))
      self.configGridWidth[axis].editingFinished.connect(partial(self.changeGridWidth, axis = axis, minval = 0.0, maxval = 100.0))
      self.configGridStyle[axis].activated.connect(partial(self.setGridStyle, axis = axis))
      self.configGridDashStyle[axis].activated.connect(partial(self.setGridDashStyle, axis = axis))
      self.configGridOrder[axis].activated.connect(partial(self.setGridOrder, axis = axis))
      
    # legend config
    self.configLegendCheck.stateChanged.connect(self.setLegend)
    self.configLegendPlacement.activated.connect(self.setLegendPlacement)
    for prop in ['face', 'edge']:
      self.configLegendColor[prop].clicked.connect(partial(self.changeLegendColor, prop))
    self.configLegendEdgeWidth.editingFinished.connect(partial(self.changeLegendEdgeWidth, minval = 0.0, maxval = 100.0))
    self.configLegendShadowCheck.stateChanged.connect(self.setLegendShadow)
    self.configLegendLabelColor.clicked.connect(self.changeLegendLabelColor)
    self.configLegendLabelSize.editingFinished.connect(partial(self.changeLegendLabelSize, entryfield = self.configLegendLabelSize, minval = 0.0, maxval = 100.0))
    self.configLegendLabelFont.activated.connect(self.setLegendLabelFont)
    
    # canvas config
    self.configFigureColorButton.clicked.connect(self.changeFigureColor)  
    self.configCanvasColorButton.clicked.connect(self.changeCanvasColor)
    
    # canvas dimensions
    self.exportSizeX.editingFinished.connect(partial(self.checkExportSize, entryfield = self.exportSizeX, axis='x', minval = 0.0, maxval = 500.0))
    self.exportSizeY.editingFinished.connect(partial(self.checkExportSize, entryfield = self.exportSizeY, axis='y', minval = 0.0, maxval = 500.0))
    self.exportSizeCurrentButton.clicked.connect(self.useCurrentDim)
    
    # pad graphics
    for axis in ['bottom', 'left']:
      self.exportPadEntry[axis].editingFinished.connect(partial(self.changePadding, axis = axis, minval = 0.0, maxval = 0.49))
    for axis in ['top', 'right']:
      self.exportPadEntry[axis].editingFinished.connect(partial(self.changePadding, axis = axis, minval = 0.50, maxval = 1.00))
    
    # xkcd
    self.configXkcdCheck.stateChanged.connect(partial(self.setXkcd,True))
    self.xkcdScale.editingFinished.connect(partial(self.checkXkcdSetting, entryfield = self.xkcdScale, item='scale', minval = 0.0, maxval = 10.0))
    self.xkcdLength.editingFinished.connect(partial(self.checkXkcdSetting, entryfield = self.xkcdLength, item='length', minval = 0.0, maxval = 1000.0))
    self.xkcdRandom.editingFinished.connect(partial(self.checkXkcdSetting, entryfield = self.xkcdRandom, item='random', minval = 0.0, maxval = 10.0))
    
    # path effects
    self.configPathEffectsCheck.stateChanged.connect(partial(self.setPathStroke, True))
    self.configPathEffectsColorButton.clicked.connect(self.changePathStrokeColor)
    self.configPathEffectsWidth.editingFinished.connect(partial(self.changePathStrokeWidth, minval = 0.0, maxval = 100.0))

    self.configPathShadowCheck.stateChanged.connect(partial(self.setPathShadow, True))
    self.configPathShadowColorButton.clicked.connect(self.changePathShadowColor)
    self.configPathShadowOffX.editingFinished.connect(partial(self.changePathShadowOffset, direction = 'x', minval = -50.0, maxval = 50.0))
    self.configPathShadowOffY.editingFinished.connect(partial(self.changePathShadowOffset, direction = 'y', minval = -50.0, maxval = 50.0))

    # preview and export graphics
    self.previewButton.clicked.connect(self.previewThis)
    self.exportButton.clicked.connect(self.exportThis)
    
    # load/save style
    self.loadStyleSet.clicked.connect(partial(self.processStyleSet, 'load', 'file'))
    self.saveStyleSet.clicked.connect(partial(self.processStyleSet,'save', 'file'))

  def processStyleSet(self, operation='load', modus='file', zoffsetData=0, zoffsetCurve=0, redraw=True):
    # loads/saves style set
    if(operation in ['load', 'save']):
      # items in plot style to save
      items = ['labelX', 'labelXColor', 'labelXSize', 'labelY', 'labelYColor', 'labelYSize',\
        'labelXAlignment', 'labelYAlignment', 'labelXPad', 'labelYPad', 'labelXPos', 'labelYPos', 'labelXAngle', 'labelYAngle',\
        'axisVisible', 'axisColor', 'axisWidth', 'axisStyle', 'axisDashStyle', 'ticksX', 'ticksXColor', 'ticksXSize', 'ticksXAngle', 'ticksXLabel', 'ticksXAuto',\
        'ticksY', 'ticksYColor', 'ticksYSize', 'ticksYAngle', 'ticksYAuto','ticksResidY', 'ticksResidYAuto', 'ticksVisible', 'ticksDirection', 'ticksColor', 'ticksWidth',\
        'ticksLength', 'gridVisible', 'gridColor', 'gridWidth', 'gridStyle', 'gridDashStyle', 'gridOrder', \
        'figureColor', 'canvasColor', 'exportWidth', 'exportHeight', 'axisFont', 'tickFont', 'padSize',\
        'legendVisible', 'legendPlacement', 'legendColor', 'legendEdgeWidth', 'legendShadow', 'legendLabelColor',\
        'legendLabelSize', 'legendLabelFont', 'xkcd', 'xkcdScale', 'xkcdLength', 'xkcdRandomness',\
        'applyPathStroke', 'pathStrokeWidth', 'pathStrokeColor',\
        'applyPathShadow', 'pathShadowX', 'pathShadowY', 'pathShadowColor',\
        'arrowVisible', 'arrowOverhang', 'arrowColor', 'arrowFill', 'arrowHeadLength', 'arrowHeadWidth', 'arrowOffset']
      dataobject = ['dataSet', 'dataError', 'dataBar', 'dataStack']
      fitobject = 'curve'
      residobject = 'resid'
      residobjectzero = 'residZero'
      flag = True
      
      if(operation == 'load'):
        # store original axis limits to counteract rescaling when applying styles
        minX, maxX, minY, maxY = self.parent.plotArea.minX, self.parent.plotArea.maxX, self.parent.plotArea.minY, self.parent.plotArea.maxY
        minResidY, maxResidY = self.parent.plotArea.minResidY, self.parent.plotArea.maxResidY
        # load from file or from string?
        if(modus == 'file'):
          filename, filter_ = QtWidgets.QFileDialog.getOpenFileName(self, filter = 'Style set (*.style)', directory = WORKINGDIR + PATH_SEPARATOR + 'styles' + PATH_SEPARATOR, caption='Open Style Sheet')
          filename = str(filename)
          try:
            loadhandle = open(filename,'r', encoding='utf-8')
            lines = loadhandle.readlines()
            loadhandle.close()
          except:
            self.parent.statusbar.showMessage('Cannot load ' + filename, self.parent.STATUS_TIME)
            lines = []
            flag = False
        else:
          lines = modus.split('\n')
        
        if(flag):
          entry = ''
          for red in lines:
            if(red.find('>>>') == 0):
              entry = red[3:].strip()
            elif(entry != ''):
              red = red.strip()
              # convert string input to original data
              try:
                red = ast.literal_eval(red)
                # assign value to plot canvas
                if(hasattr(self.parent.plotArea, entry)):
                  setattr(self.parent.plotArea, entry, red)
              except:
                self.parent.statusbar.showMessage('Failed to restore setting ' + repr(entry) + repr(red), self.parent.STATUS_TIME)
              entry = ''
              
          # loadconfig of data set and curve
          entry = ''
          for red in lines:
            if(red.find('>>>') == 0):
              entry = red[3:].strip()
            elif(entry != ''):
              if('_' in entry):
                splitentry = entry.split('_')
                entry = splitentry[0]; index = int(splitentry[-1])
                
              if((entry in dataobject) or (entry in [fitobject, residobject, residobjectzero])):
                red = red.strip()
                # convert string input to original data
                try:
                  red = ast.literal_eval(red)
                  for key in red:
                    if((entry == dataobject[0]) and (index + zoffsetData < len(self.parent.data))):
                      self.parent.data[index + zoffsetData].setStyle(key, red[key], redraw=False)
                    elif((entry == dataobject[1]) and (index + zoffsetData < len(self.parent.data))):
                      self.parent.data[index + zoffsetData].setErrorStyle(key, red[key], redraw=False)
                    elif((entry == dataobject[2]) and (index + zoffsetData < len(self.parent.data))):
                      self.parent.data[index + zoffsetData].setBarStyle(key, red[key], redraw=False)
                    elif((entry == dataobject[3]) and (index + zoffsetData < len(self.parent.data))):
                      self.parent.data[index + zoffsetData].setStackStyle(key, red[key], redraw=False)
                    elif((entry == residobject) and (index + zoffsetData < len(self.parent.data))):
                      self.parent.data[index + zoffsetData].setResidStyle(key, red[key], redraw=False)
                    elif((entry == residobjectzero) and (index + zoffsetData < len(self.parent.data))):
                      self.parent.data[index + zoffsetData].setResidLineStyle(key, red[key], redraw=False)
                    elif((entry == fitobject) and (index + zoffsetCurve < len(self.parent.fit))):
                      self.parent.fit[index + zoffsetCurve].setStyle(key, red[key], redraw=False)
                except:
                  self.parent.statusbar.showMessage('Failed to restore setting' + repr(entry) + repr(red), self.parent.STATUS_TIME)
  
              entry = ''
  
          # cause plot to be redrawn
          self.parent.plotArea.initPlot(initialize=False)
          # update entry fields
          self.updateFields(initialize=False)
          
          # rescale to original axis limits
          self.parent.plotArea.setAxisLimits(lower=minX, upper=maxX, axis='x', updateLabel=True, target='plot', redraw=False)
          self.parent.plotArea.setAxisLimits(lower=minY, upper=maxY, axis='y', updateLabel=True, target='plot', redraw=False)
          self.parent.plotArea.setAxisLimits(lower=minResidY, upper=maxResidY, axis='y', updateLabel=True, target='resid', redraw=False)

          # separately deal with legend so that it updates
          value = self.parent.plotArea.legendVisible
          self.parent.plotArea.setLegend(value=value, redraw=redraw)
          
          # update resid plot?
          if(redraw):
            self.parent.plotArea.residplotwidget.myRefresh()
      else:
        # retrieve plot configuration
        red = ''
        for entry in items:
          if(hasattr(self.parent.plotArea, entry)):
            red += '>>>' + entry + '\n'
            tempOut = self.parent.plotArea.__dict__[entry]
            if(hasattr(tempOut, 'tolist')):
              tempOut = tempOut.tolist()
            red += repr(tempOut)+'\n'
        # save config of data set and curve
        for index in range(len(self.parent.data)):
          red += '>>>' + dataobject[0] + '_' + str(index) + '\n'
          red += repr(self.parent.data[index].getStyle()) + '\n'
          red += '>>>' + dataobject[1] + '_' + str(index) + '\n'
          red += repr(self.parent.data[index].getErrorStyle()) + '\n'
          red += '>>>' + dataobject[2] + '_' + str(index) + '\n'
          red += repr(self.parent.data[index].getBarStyle()) + '\n'
          red += '>>>' + dataobject[3] + '_' + str(index) + '\n'
          red += repr(self.parent.data[index].getStackStyle()) + '\n'
          red += '>>>' + residobject + '_' + str(index) + '\n'
          red += repr(self.parent.data[index].getResidStyle()) + '\n'
          red += '>>>' + residobjectzero + '_' + str(index) + '\n'
          red += repr(self.parent.data[index].getResidLineStyle()) + '\n'
        
        for index in range(len(self.parent.fit)):
          red += '>>>' + fitobject + '_' + str(index) + '\n'
          red += repr(self.parent.fit[index].getStyle()) + '\n'


        if (modus == 'file'):
          filename, fitler_ = QtWidgets.QFileDialog.getSaveFileName(self, filter = 'Style set (*.style)', directory = WORKINGDIR + PATH_SEPARATOR + 'styles' + PATH_SEPARATOR, caption='Save Style Sheet')
          filename = str(filename)
          try:
            savehandle=open(filename,'w', encoding='utf-8')
            savehandle.write(red)
            savehandle.close()
          except:
            self.parent.statusbar.showMessage('Cannot write ' + filename, self.parent.STATUS_TIME)
        else:
          return red
          
  def changePadding(self, axis='bottom', minval=0, maxval=1):
    # adjusts padding around figure
    if(axis in ['bottom', 'top', 'left', 'right']):
      # check paramter boundaries
      try:
        value = float(self.exportPadEntry[axis].text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        self.exportPadEntry[axis].setText(str(value))
        
      self.parent.plotArea.setPadding(value=value, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setPadding(value=value, axis=axis, redraw=True, target='resid')

  def changeArrowHeadWidth(self, axis='x', minval = 0.0, maxval = 1.0):
    # changes arro head width
    if(axis in ['x', 'y']):
      # check paramter boundaries
      try:
        value = float(self.configArrowHeadWidth[axis].text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        self.configArrowHeadWidth[axis].setText(str(value))
        
      self.parent.plotArea.setAxisArrowHeadWidth(value=value, axis=axis, redraw=True)

  def changeArrowHeadLength(self, axis='x', minval = 0.0, maxval = 1.0):
    # changes arrow head length
    if(axis in ['x', 'y']):
      # check paramter boundaries
      try:
        value = float(self.configArrowHeadLength[axis].text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        self.configArrowHeadLength[axis].setText(str(value))
        
      self.parent.plotArea.setAxisArrowHeadLength(value=value, axis=axis, redraw=True)

  def changeArrowOverhang(self, axis='x', minval = -1.0, maxval = 1.0):
    # changes arrow head overhang
    if(axis in ['x', 'y']):
      # check paramter boundaries
      try:
        value = float(self.configArrowOverhang[axis].text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        self.configArrowOverhang[axis].setText(str(value))
        
      self.parent.plotArea.setAxisArrowOverhang(value=value, axis=axis, redraw=True)

  def changeArrowOffset(self, axis='x', minval = 0.0, maxval = 1.0):
    # changes arrow head offset
    if(axis in ['x', 'y']):
      # check paramter boundaries
      try:
        value = float(self.configArrowOffset[axis].text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        self.configArrowOffset[axis].setText(str(value))
        
      self.parent.plotArea.setAxisArrowOffset(value=value, axis=axis, redraw=True)

  def changeArrowColor(self, axis='x', item='fill'):
    # sets arrow color(s)
    if((axis in ['x', 'y']) and (item in ['fill', 'line'])):
      # get current color
      if(item == 'line'):
        prevColor = [255*i for i in self.parent.plotArea.arrowColor[axis]]
      else:
        prevColor = [255*i for i in self.parent.plotArea.arrowFill[axis]]
      prevColor = QtGui.QColor(*prevColor)
      # call QColor dialog
      nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
      if (nuColor.isValid()):
        value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
        value = [i/255.0 for i in value]
        self.parent.plotArea.setAxisArrowColor(value=value, axis=axis, item=item, redraw=True)
        # update color button
        if(item == 'line'):
          colorvalue = [int(i*255.0) for i in self.parent.plotArea.arrowColor[axis][0:3]]
          colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
          self.configArrowLineColor[axis].setStyleSheet(colorstr)
        else:
          colorvalue = [int(i*255.0) for i in self.parent.plotArea.arrowFill[axis][0:3]]
          colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
          self.configArrowFillColor[axis].setStyleSheet(colorstr)      

  def setAxisArrow(self, axis='x'):
    # toggles arrow visibility
    if(axis in ['x', 'y']):
      state = self.configArrowCheck[axis].isChecked()
      for target in ['plot', 'resid']:
        self.parent.plotArea.setAxisArrow(state=state, axis=axis, redraw=True, target=target)

  def setPathStroke(self, redraw=True):
    # toggles path effects
    state = self.configPathEffectsCheck.isChecked()
    self.parent.plotArea.setPathStroke(state=state, redraw=redraw)

  def changePathStrokeColor(self):
    # changes color of path stroke
    # get current color
    prevColor = [255*i for i in self.parent.plotArea.pathStrokeColor]
    prevColor = QtGui.QColor(*prevColor)
    # call QColor dialog
    nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
    if (nuColor.isValid()):
      value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
      value = [i/255.0 for i in value]
      self.parent.plotArea.setPathStrokeColor(value=value, redraw=True)
      # update color button
      colorvalue = [int(i*255.0) for i in self.parent.plotArea.pathStrokeColor[0:3]]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.configPathEffectsColorButton.setStyleSheet(colorstr)

  def changePathStrokeWidth(self, minval = 0.0, maxval = 100.0):
    # changes path stroke width
    # check paramter boundaries
    try:
      value = float(self.configPathEffectsWidth.text())
      originalvalue = value
    except:
      value = 0.0
      originalvalue = 1.0
    value = np.min((value, maxval))
    value = np.max((value, minval))
    # update parameters
    if (value != originalvalue):
      self.configPathEffectsWidth.setText(str(value))
      
    self.parent.plotArea.setPathStrokeWidth(value=value, redraw=True)

  def setPathShadow(self, redraw=True):
    # toggles path effects
    state = self.configPathShadowCheck.isChecked()
    self.parent.plotArea.setPathShadow(state=state, redraw=redraw)

  def changePathShadowColor(self):
    # changes color of path shadow
    # get current color
    prevColor = [255*i for i in self.parent.plotArea.pathShadowColor]
    prevColor = QtGui.QColor(*prevColor)
    # call QColor dialog
    nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
    if (nuColor.isValid()):
      value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
      value = [i/255.0 for i in value]
      self.parent.plotArea.setPathShadowColor(value=value, redraw=True)
      # update color button
      colorvalue = [int(i*255.0) for i in self.parent.plotArea.pathShadowColor[0:3]]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.configPathShadowColorButton.setStyleSheet(colorstr)

  def changePathShadowOffset(self, direction = 'x', minval = 0.0, maxval = 100.0):
    # changes path shadow offset
    if(direction in ['x', 'y']):
      # check paramter boundaries
      if(direction == 'x'):
        try:
          value = float(self.configPathShadowOffX.text())
          originalvalue = value
        except:
          value = 0.0
          originalvalue = 1.0
      else:
        try:
          value = float(self.configPathShadowOffY.text())
          originalvalue = value
        except:
          value = 0.0
          originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        if(direction == 'x'):
          self.configPathShadowOffX.setText(str(value))
        else:
          self.configPathShadowOffY.setText(str(value))
        
      self.parent.plotArea.setPathShadowOffset(value=value, direction=direction, redraw=True)

  def setXkcd(self, redraw=True):
    # toggles Xkcd
    state = self.configXkcdCheck.isChecked()
    self.parent.plotArea.xkcdify(state=state, redraw=redraw)

  def setLegend(self):
    # toggles visibility of legend
    state = self.configLegendCheck.isChecked()
    self.parent.plotArea.setLegend(value=state, redraw=True, target='plot')

  def setLegendShadow(self):
    # toggles visibility of legend shadow
    state = self.configLegendShadowCheck.isChecked()
    self.parent.plotArea.setLegendShadow(value=state, redraw=True, target='plot')

  def setLegendPlacement(self):
    # toggles visibility of legend
    placement = str(self.configLegendPlacement.currentText())
    self.parent.plotArea.setLegendPlacement(value=placement, redraw=True, target='plot')

  def changeLegendColor(self, prop='face'):
    # sets color of legend box
    if(prop in ['face', 'edge']):
      # get current color
      prevColor = [255*i for i in self.parent.plotArea.legendColor[prop]]
  
      prevColor = QtGui.QColor(*prevColor)
      # call QColor dialog
      nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
      if (nuColor.isValid()):
        value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
        value = [i/255.0 for i in value]
        self.parent.plotArea.setLegendColor(value=value, prop=prop, redraw=True, target='plot')
        # update color button
        colorvalue = [int(i*255.0) for i in self.parent.plotArea.legendColor[prop]]
        colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
        self.configLegendColor[prop].setStyleSheet(colorstr)

  def changeLegendLabelColor(self):
    # sets color of legend labels
    # get current color
    prevColor = [255*i for i in self.parent.plotArea.legendLabelColor]

    prevColor = QtGui.QColor(*prevColor)
    # call QColor dialog
    nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
    if (nuColor.isValid()):
      value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
      value = [i/255.0 for i in value]
      self.parent.plotArea.setLegendLabelColor(value=value, redraw=True, target='plot')
      # update color button
      colorvalue = [int(i*255.0) for i in self.parent.plotArea.legendLabelColor]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.configLegendLabelColor.setStyleSheet(colorstr)

  def changeLegendEdgeWidth(self, minval=0, maxval=1):
    # changes width of legend edge
    # check paramter boundaries
    try:
      value = float(self.configLegendEdgeWidth.text())
      originalvalue = value
    except:
      value = 0.0
      originalvalue = 1.0
    value = np.min((value, maxval))
    value = np.max((value, minval))
    # update parameters
    if (value != originalvalue):
      self.configLegendEdgeWidth.setText(str(value))
      
    self.parent.plotArea.setLegendEdgeWidth(value=value, redraw=True, target='plot')

  def changeLegendLabelSize(self, entryfield=None, minval=0, maxval=1):
    # changes font size of legend label
    try:
      value = float(entryfield.text())
      originalvalue = value
    except:
      value = 0.0
      originalvalue = 1.0
    value = np.min((value, maxval))
    value = np.max((value, minval))
    # update parameters
    if (value != originalvalue):
      entryfield.setText(str(value))
      
    self.parent.plotArea.setLegendLabelSize(value=value, redraw=True, target='plot')

  def setLegendLabelFont(self):
    # sets legend label font
    useFont = str(self.configLegendLabelFont.currentText())
      
    if(useFont in self.parent.fontNames):
      self.parent.plotArea.setLegendLabelFont(value=useFont, redraw=True, target='plot')

  def setGridVisibility(self, axis='x'):
    # toggles grid visibility
    if(axis in ['x', 'y']):
      state = self.configGridCheck[axis].isChecked()
      self.parent.plotArea.setGridVisibility(value=state, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setGridVisibility(value=state, axis=axis, redraw=True, target='resid')

  def changeGridColor(self, axis='x'):
    # sets grid color
    if(axis in ['x', 'y']):
      # get current color
      prevColor = [255*i for i in self.parent.plotArea.gridColor[axis]]
  
      prevColor = QtGui.QColor(*prevColor)
      # call QColor dialog
      nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
      if (nuColor.isValid()):
        value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
        value = [i/255.0 for i in value]
        self.parent.plotArea.setGridColor(value=value, axis=axis, redraw=True, target='plot')
        self.parent.plotArea.setGridColor(value=value, axis=axis, redraw=True, target='resid')
        # update color button
        colorvalue = [int(i*255.0) for i in self.parent.plotArea.gridColor[axis]]
        colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
        self.configGridColor[axis].setStyleSheet(colorstr)

  def changeGridWidth(self, axis='x', minval=0, maxval=1):
    # changes grid line width
    if(axis in ['x', 'y']):
      # check paramter boundaries
      try:
        value = float(self.configGridWidth[axis].text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        self.configGridWidth[axis].setText(str(value))
        
      self.parent.plotArea.setGridWidth(value=value, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setGridWidth(value=value, axis=axis, redraw=True, target='resid')

  def setGridOrder(self, axis = 'x'):
    # sets grid style
    if(axis in ['x', 'y']):
      order = str(self.configGridOrder[axis].currentText())
      index = self.configGridOrder[axis].currentIndex()
      for entry in ['x', 'y']:
        # have to temporarily disable event logging
        self.configGridOrder[entry].blockSignals(True)
        self.configGridOrder[entry].setCurrentIndex(index)
        self.configGridOrder[entry].blockSignals(False)
     
      self.parent.plotArea.setGridOrder(value=order, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setGridOrder(value=order, axis=axis, redraw=True, target='resid')

  def setGridStyle(self, axis = 'x'):
    # sets grid style
    if(axis in ['x', 'y']):
      style = str(self.configGridStyle[axis].currentText())
      self.parent.plotArea.setGridStyle(value=style, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setGridStyle(value=style, axis=axis, redraw=True, target='resid')

  def setGridDashStyle(self, axis = 'x'):
    # sets grid style
    if(axis in ['x', 'y']):
      style = str(self.configGridDashStyle[axis].currentText())
      self.parent.plotArea.setGridDashStyle(value=style, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setGridDashStyle(value=style, axis=axis, redraw=True, target='resid')

  def changeAxisColor(self, axis='left'):
    # sets axis color
    if(axis in ['left', 'right', 'top', 'bottom']):
      # get current color
      prevColor = [255*i for i in self.parent.plotArea.axisColor[axis]]
  
      prevColor = QtGui.QColor(*prevColor)
      # call QColor dialog
      nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
      if (nuColor.isValid()):
        value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
        value = [i/255.0 for i in value]
        self.parent.plotArea.setAxisColor(value=value, axis=axis, redraw=True, target='plot')
        self.parent.plotArea.setAxisColor(value=value, axis=axis, redraw=True, target='resid')
        # update color button
        colorvalue = [int(i*255.0) for i in self.parent.plotArea.axisColor[axis]]
        colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
        self.configAxisColor[axis].setStyleSheet(colorstr)

  def setTickFont(self, axis='x'):
    # sets tick font
    if(axis in ['x', 'y']):
      if(axis == 'x'):
        useFont = str(self.configTickXFont.currentText())
      else:
        useFont = str(self.configTickYFont.currentText())
      
      if(useFont in self.parent.fontNames):
        self.parent.plotArea.setTickFont(value=useFont, axis=axis, redraw=True, target='plot')
        self.parent.plotArea.setTickFont(value=useFont, axis=axis, redraw=True, target='resid')

  def setAxisLabelAlignment(self, axis='x'):
    # sets alignment of axis label
    if(axis in ['x', 'y']):
      flag = False
      if(axis == 'x'):
        useAlignment = str(self.configXAlignment.currentText())
        if(useAlignment in self.alignHorizontal):
          flag = True
      else:
        useAlignment = str(self.configYAlignment.currentText())
        if(useAlignment in self.alignVertical):
          flag = True
      
      if(flag):
        self.parent.plotArea.setAxisLabelAlignment(value=useAlignment, axis=axis, redraw=True, target='plot')
        self.parent.plotArea.setAxisLabelAlignment(value=useAlignment, axis=axis, redraw=True, target='resid')

  def setAxisFont(self, axis='x'):
    # sets axis font
    if(axis in ['x', 'y']):
      if(axis == 'x'):
        useFont = str(self.configXFont.currentText())
      else:
        useFont = str(self.configYFont.currentText())
      
      if(useFont in self.parent.fontNames):
        self.parent.plotArea.setAxisFont(value=useFont, axis=axis, redraw=True, target='plot')
        self.parent.plotArea.setAxisFont(value=useFont, axis=axis, redraw=True, target='resid')

  def setAxisStyle(self, axis='left'):
    # sets axis style
    if(axis in ['left', 'right', 'top', 'bottom']):
      style = str(self.configAxisStyle[axis].currentText())
      self.parent.plotArea.setAxisStyle(value=style, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setAxisStyle(value=style, axis=axis, redraw=True, target='resid')

  def setAxisDashStyle(self, axis='left'):
    # sets axis style
    if(axis in ['left', 'right', 'top', 'bottom']):
      style = str(self.configAxisDashStyle[axis].currentText())
      self.parent.plotArea.setAxisDashStyle(value=style, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setAxisDashStyle(value=style, axis=axis, redraw=True, target='resid')

  def changeAxisWidth(self, axis='left', minval=0, maxval=1):
    # changes axis width
    if(axis in ['left', 'right', 'top', 'bottom']):
      # check paramter boundaries
      try:
        value = float(self.configAxisWidth[axis].text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        self.configAxisWidth[axis].setText(str(value))
        
      self.parent.plotArea.setAxisWidth(value=value, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setAxisWidth(value=value, axis=axis, redraw=True, target='resid')

  def setAxisVisibility(self, axis='left'):
    # toggles axis visibility
    if(axis in ['left', 'right', 'top', 'bottom']):
      state = self.configAxisCheck[axis].isChecked()
      self.parent.plotArea.setAxisVisibility(value=state, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setAxisVisibility(value=state, axis=axis, redraw=True, target='resid')

  def setTickMarkDirection(self, axis='left'):
    # sets tick mark direction
    if(axis in ['left', 'right', 'top', 'bottom']):
      style = str(self.configTickMarkDirection[axis].currentText())
      index = self.configTickMarkDirection[axis].currentIndex()
      # update parameters
      if(axis in ['left', 'right']):
        for entry in ['left', 'right']:
          # have to temporarily disable event logging
          self.configTickMarkDirection[entry].blockSignals(True)
          self.configTickMarkDirection[entry].setCurrentIndex(index)
          self.configTickMarkDirection[entry].blockSignals(False)
      else:
        for entry in ['top', 'bottom']:
          # have to temporarily disable event logging
          self.configTickMarkDirection[entry].blockSignals(True)
          self.configTickMarkDirection[entry].setCurrentIndex(index)
          self.configTickMarkDirection[entry].blockSignals(False)

      self.parent.plotArea.setTickMarkDirection(value=style, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setTickMarkDirection(value=style, axis=axis, redraw=True, target='resid')

  '''
  def setTickMarkDashStyle(self, axis='left'):
    # sets tick mark dash style
    if(axis in ['left', 'right', 'top', 'bottom']):
      style = str(self.configTickMarkDashStyle[axis].currentText())
      index = self.configTickMarkDashStyle[axis].currentIndex()
      # update parameters
      if(axis in ['left', 'right']):
        for entry in ['left', 'right']:
          # have to temporarily disable event logging
          self.configTickMarkDashStyle[entry].blockSignals(True)
          self.configTickMarkDashStyle[entry].setCurrentIndex(index)
          self.configTickMarkDashStyle[entry].blockSignals(False)
      else:
        for entry in ['top', 'bottom']:
          # have to temporarily disable event logging
          self.configTickMarkDashStyle[entry].blockSignals(True)
          self.configTickMarkDashStyle[entry].setCurrentIndex(index)
          self.configTickMarkDashStyle[entry].blockSignals(False)

      self.parent.plotArea.setTickMarkDashStyle(value=style, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setTickMarkDashStyle(value=style, axis=axis, redraw=True, target='resid')
  '''

  def setTicksVisibility(self, axis='left'):
    # toggles ticks visibility
    if(axis in ['left', 'right', 'top', 'bottom']):
      state = self.configTickMarkCheck[axis].isChecked()
      self.parent.plotArea.setTickMarkVisibility(value=state, axis=axis, redraw=False, target='plot')
      self.parent.plotArea.setTickMarkVisibility(value=state, axis=axis, redraw=False, target='resid')

      # need to reapply tick formatting as there is the possiblity we switched from left to right of from top to bottom or vice versa
      if(axis in ['top', 'bottom']):
        axis = 'x'
        tickLabelColor = self.parent.plotArea.ticksXColor
        tickLabelSize = self.parent.plotArea.ticksXSize
        tickLabelAngle = self.parent.plotArea.ticksXAngle
        tickLabelFont = self.parent.plotArea.tickFont[axis]
      else:
        axis = 'y'
        tickLabelColor = self.parent.plotArea.ticksYColor
        tickLabelSize = self.parent.plotArea.ticksYSize
        tickLabelAngle = self.parent.plotArea.ticksYAngle
        tickLabelFont = self.parent.plotArea.tickFont[axis]
      
      for target in ['plot', 'resid']:
        self.parent.plotArea.setTickLabelColor(value=tickLabelColor, axis=axis, redraw=False, target=target)
        self.parent.plotArea.setTickLabelSize(value=tickLabelSize, axis=axis, redraw=False, target=target)
        self.parent.plotArea.setTickLabelAngle(value=tickLabelAngle, axis=axis, redraw=False, target=target)
        self.parent.plotArea.setTickFont(value=tickLabelFont, axis=axis, redraw=False, target=target)
        
      # redraw
      self.parent.plotArea.dataplotwidget.myRefresh()
      self.parent.plotArea.residplotwidget.myRefresh()
      
  def changeTickMarkLength(self, axis='left', minval=0, maxval=1):
    # changes tick mark width
    if(axis in ['left', 'right', 'top', 'bottom']):
      # check paramter boundaries
      try:
        value = float(self.configTickMarkLength[axis].text())
      except:
        value = 0.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if(axis in ['left', 'right']):
        self.configTickMarkLength['left'].setText(str(value))
        self.configTickMarkLength['right'].setText(str(value))
      else:
        self.configTickMarkLength['top'].setText(str(value))
        self.configTickMarkLength['bottom'].setText(str(value))
        
      self.parent.plotArea.setTickMarkLength(value=value, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setTickMarkLength(value=value, axis=axis, redraw=True, target='resid')

  def changeTickMarkWidth(self, axis='left', minval=0, maxval=1):
    # changes tick mark width
    if(axis in ['left', 'right', 'top', 'bottom']):
      # check paramter boundaries
      try:
        value = float(self.configTickMarkWidth[axis].text())
      except:
        value = 0.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if(axis in ['left', 'right']):
        self.configTickMarkWidth['left'].setText(str(value))
        self.configTickMarkWidth['right'].setText(str(value))
      else:
        self.configTickMarkWidth['top'].setText(str(value))
        self.configTickMarkWidth['bottom'].setText(str(value))
        
      self.parent.plotArea.setTickMarkWidth(value=value, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setTickMarkWidth(value=value, axis=axis, redraw=True, target='resid')

  def changeTickMarkColor(self, axis='x'):
    # changes color of tick marks
    if(axis in ['left', 'right', 'top', 'bottom']):
      # get current color
      prevColor = [255*i for i in self.parent.plotArea.ticksColor[axis]]
  
      prevColor = QtGui.QColor(*prevColor)
      # call QColor dialog
      nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
      if (nuColor.isValid()):
        value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
        value = [i/255.0 for i in value]
        self.parent.plotArea.setTickMarkColor(value=value, axis=axis, redraw=True, target='plot')
        self.parent.plotArea.setTickMarkColor(value=value, axis=axis, redraw=True, target='resid')
        # update color button
        colorvalue = [int(i*255.0) for i in self.parent.plotArea.ticksColor[axis][0:3]]
        colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
        if(axis in ['left', 'right']):
          self.configTickMarkColor['left'].setStyleSheet(colorstr)
          self.configTickMarkColor['right'].setStyleSheet(colorstr)
        else:
          self.configTickMarkColor['top'].setStyleSheet(colorstr)
          self.configTickMarkColor['bottom'].setStyleSheet(colorstr)

  def automaticAxisTicks(self, axis='x'):
    # automatically sets axis limits
    if(axis in ['x', 'y', 'resid']):
      if(axis == 'x'):
        nuTicks = self.parent.plotArea.setAutoTicks(axis=axis, redraw=True, target='resid')
        nuTicks = self.parent.plotArea.setAutoTicks(axis=axis, redraw=True, target='plot')
        # update entryfield
        tickstr = ', '.join([str(i) for i in nuTicks])
        self.configTickXEntry.setText(tickstr)
      elif(axis=='y'):
        nuTicks = self.parent.plotArea.setAutoTicks(axis=axis, redraw=True, target='plot')
        # update entryfield
        tickstr = ', '.join([str(i) for i in nuTicks])
        self.configTickYEntry.setText(tickstr)
      else:
        nuTicks = self.parent.plotArea.setAutoTicks(axis=axis, redraw=True, target='resid')
        # update entryfield
        tickstr = ', '.join([str(i) for i in nuTicks])
        self.configTickResidYEntry.setText(tickstr)

  def dataAxisTicks(self):
    # set x ticks to label values
    currDataSet = self.parent.activeData
    self.parent.plotArea.setDataAxisTicks(currDataSet, redraw=True, target='plot')
    self.parent.plotArea.setDataAxisTicks(currDataSet, redraw=True, target='resid')

  def useCurrentDim(self):
    # sets export dimensions to current dimensions on screen
    # obtain current dimensions
    currwidth, currheight = self.parent.plotArea.matplot.get_size_inches()
    self.exportSizeX.setText(str(currwidth))
    self.exportSizeY.setText(str(currheight))
    self.parent.plotArea.exportWidth = currwidth
    self.parent.plotArea.exportHeight = currheight

  def checkXkcdSetting(self, entryfield=None, item='scale', minval=0, maxval=1):
    # restrains dimensions for figure export
    try:
      value = float(entryfield.text())
      originalvalue = value
    except:
      value = 0.0
      originalvalue = 1.0
    value = np.min((value, maxval))
    value = np.max((value, minval))
    # update parameters
    if (value != originalvalue):
      entryfield.setText(str(value))
      
    self.parent.plotArea.setXkcdSetting(value=value, item=item, redraw=True)
    
  def checkExportSize(self, entryfield=None, axis='x', minval=0, maxval=1):
    # restrains dimensions for figure export
    try:
      value = float(entryfield.text())
      originalvalue = value
    except:
      value = 0.0
      originalvalue = 1.0
    value = np.min((value, maxval))
    value = np.max((value, minval))
    # update parameters
    if (value != originalvalue):
      entryfield.setText(str(value))
      
    if(axis=='x'):
      self.parent.plotArea.exportWidth = value
    elif(axis=='y'):
      self.parent.plotArea.exportHeight = value
        
  def changeAxisTicks(self, axis='x'):
    if(axis in ['x', 'y', 'resid']):
      if(axis == 'x'):
        entryfield = self.configTickXEntry
      elif(axis == 'y'):
        entryfield = self.configTickYEntry
      else:
        entryfield = self.configTickResidYEntry
      
      tickstr = str(entryfield.text())
      # process new tick string
      nuTicks = tickstr.split(',')
      nuTicks = [i.strip() for i in nuTicks]
      
      # convert to floats
      nuTicks_num = []
      for entry in nuTicks:
        if(self.parent.isNumber(entry)):
          nuTicks_num.append(float(entry))
      nuTicks_num = np.array(sorted(nuTicks_num))

      # update entryfield
      tickstr = ', '.join([str(i) for i in nuTicks_num])
      entryfield.setText(tickstr)
      
      # set ticks in plot
      if(axis == 'x'):
        self.parent.plotArea.setAxisTicks(value=nuTicks_num, axis=axis, redraw=True, target='plot')
        self.parent.plotArea.setAxisTicks(value=nuTicks_num, axis=axis, redraw=True, target='resid')
      elif(axis == 'y'):
        self.parent.plotArea.setAxisTicks(value=nuTicks_num, axis=axis, redraw=True, target='plot')
      else:
        self.parent.plotArea.setAxisTicks(value=nuTicks_num, axis=axis, redraw=True, target='resid')

  def changeTickLabelAngle(self, entryfield=None, axis='x', minval=0, maxval=1):
    if(axis in ['x', 'y']):
      # check paramter boundaries
      try:
        value = float(entryfield.text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        entryfield.setText(str(value))
        
      self.parent.plotArea.setTickLabelAngle(value=value, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setTickLabelAngle(value=value, axis=axis, redraw=True, target='resid')

  def changeTickLabelSize(self, entryfield=None, axis='x', minval=0, maxval=1):
    if(axis in ['x', 'y']):
      # check paramter boundaries
      try:
        value = float(entryfield.text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        entryfield.setText(str(value))
        
      self.parent.plotArea.setTickLabelSize(value=value, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setTickLabelSize(value=value, axis=axis, redraw=True, target='resid')

  def changeAxisLabelAngle(self, entryfield=None, axis='x', minval=0, maxval=1):
    if(axis in ['x', 'y']):
      # check paramter boundaries
      try:
        value = float(entryfield.text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        entryfield.setText(str(value))
        
      self.parent.plotArea.setAxisLabelAngle(value=value, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setAxisLabelAngle(value=value, axis=axis, redraw=True, target='resid')

  def changeAxisLabelPad(self, entryfield=None, axis='x', minval=0, maxval=1):
    if(axis in ['x', 'y']):
      # check paramter boundaries
      try:
        value = float(entryfield.text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        entryfield.setText(str(value))
        
      self.parent.plotArea.setAxisLabelPad(value=value, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setAxisLabelPad(value=value, axis=axis, redraw=True, target='resid')

  def changeAxisLabelPos(self, entryfield=None, axis='x', minval=0, maxval=1):
    if(axis in ['x', 'y']):
      # check paramter boundaries
      try:
        value = float(entryfield.text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        entryfield.setText(str(value))
        
      self.parent.plotArea.setAxisLabelPos(value=value, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setAxisLabelPos(value=value, axis=axis, redraw=True, target='resid')

  def changeAxisLabelSize(self, entryfield=None, axis='x', minval=0, maxval=1):
    if(axis in ['x', 'y']):
      # check paramter boundaries
      try:
        value = float(entryfield.text())
        originalvalue = value
      except:
        value = 0.0
        originalvalue = 1.0
      value = np.min((value, maxval))
      value = np.max((value, minval))
      # update parameters
      if (value != originalvalue):
        entryfield.setText(str(value))
        
      self.parent.plotArea.setAxisLabelSize(value=value, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setAxisLabelSize(value=value, axis=axis, redraw=True, target='resid')

  def HLine(self):
    # draws a horizontal line
    hline = QtWidgets.QFrame()
    hline.setFrameShape(QtWidgets.QFrame.HLine)
    hline.setFrameShadow(QtWidgets.QFrame.Sunken)
    return hline

  def VLine(self):
    # draws a horizontal line
    vline = QtWidgets.QFrame()
    vline.setFrameShape(QtWidgets.QFrame.VLine)
    vline.setFrameShadow(QtWidgets.QFrame.Sunken)
    return vline

  def changeFigureColor(self):
    # changes color of canvas
    # get current color
    prevColor = [255*i for i in self.parent.plotArea.figureColor]

    prevColor = QtGui.QColor(*prevColor)
    # call QColor dialog
    nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
    if (nuColor.isValid()):
      value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
      value = [i/255.0 for i in value]
      self.parent.plotArea.setFigureColor(value=value, redraw=True, target='plot')
      self.parent.plotArea.setFigureColor(value=value, redraw=True, target='resid')
      # update color button
      colorvalue = [int(i*255.0) for i in self.parent.plotArea.figureColor[0:3]]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.configFigureColorButton.setStyleSheet(colorstr)
    
  def changeCanvasColor(self):
    # changes color of canvas
    # get current color
    prevColor = [255*i for i in self.parent.plotArea.canvasColor]

    prevColor = QtGui.QColor(*prevColor)
    # call QColor dialog
    nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
    if (nuColor.isValid()):
      value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
      value = [i/255.0 for i in value]
      self.parent.plotArea.setCanvasColor(value=value, redraw=True, target='plot')
      self.parent.plotArea.setCanvasColor(value=value, redraw=True, target='resid')
      # update color button
      colorvalue = [int(i*255.0) for i in self.parent.plotArea.canvasColor[0:3]]
      colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
      self.configCanvasColorButton.setStyleSheet(colorstr)
    
  def changeTickLabelColor(self, axis='x'):
    # changes color of axis ticks
    if(axis in ['x', 'y']):
      # get current color
      if(axis == 'x'):
        prevColor = [255*i for i in self.parent.plotArea.ticksXColor]
      else:
        prevColor = [255*i for i in self.parent.plotArea.ticksYColor]
  
      prevColor = QtGui.QColor(*prevColor)
      # call QColor dialog
      nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
      if (nuColor.isValid()):
        value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
        value = [i/255.0 for i in value]
        self.parent.plotArea.setTickLabelColor(value=value, axis=axis, redraw=True, target='plot')
        self.parent.plotArea.setTickLabelColor(value=value, axis=axis, redraw=True, target='resid')
        # update color button
        if (axis == 'x'):
          colorvalue = [int(i*255.0) for i in self.parent.plotArea.ticksXColor[0:3]]
          colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
          self.configTickXColorButton.setStyleSheet(colorstr)
        else:
          colorvalue = [int(i*255.0) for i in self.parent.plotArea.ticksYColor[0:3]]
          colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
          self.configTickYColorButton.setStyleSheet(colorstr)

  def changeAxisLabelColor(self, axis='x'):
    # changes color of axis label
    if(axis in ['x', 'y']):
      # get current color
      if(axis == 'x'):
        prevColor = [255*i for i in self.parent.plotArea.labelXColor]
      else:
        prevColor = [255*i for i in self.parent.plotArea.labelYColor]
  
      prevColor = QtGui.QColor(*prevColor)
      # call QColor dialog
      nuColor = QtWidgets.QColorDialog.getColor(prevColor, self, 'Set Color', QtWidgets.QColorDialog.ShowAlphaChannel)
      if (nuColor.isValid()):
        value = [nuColor.red(), nuColor.green(), nuColor.blue(), nuColor.alpha()]
        value = [i/255.0 for i in value]
        self.parent.plotArea.setAxisLabelColor(value=value, axis=axis, redraw=True, target='plot')
        self.parent.plotArea.setAxisLabelColor(value=value, axis=axis, redraw=True, target='resid')
        # update color button
        if (axis == 'x'):
          colorvalue = [int(i*255.0) for i in self.parent.plotArea.labelXColor[0:3]]
          colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
          self.configXColorButton.setStyleSheet(colorstr)
        else:
          colorvalue = [int(i*255.0) for i in self.parent.plotArea.labelYColor[0:3]]
          colorstr = 'background-color: rgb(%d, %d, %d);'%(colorvalue[0], colorvalue[1], colorvalue[2])
          self.configYColorButton.setStyleSheet(colorstr)

  def changeAxisLabel(self, axis='x'):
    # updates axis label
    if(axis in ['x', 'y']):
      if(axis == 'x'):
        labeltext = str(self.configXName.text())
        # encode/recode to process newlines correctly
        #labeltext = labeltext.encode('utf-8').decode('unicode-escape')
        labeltext2 = labeltext
      else:
        labeltext = str(self.configYName.text())
        #labeltext = labeltext.encode('utf-8').decode('unicode-escape')
        labeltext2 = labeltext
 
      self.parent.plotArea.setAxisLabel(labeltext=labeltext, axis=axis, redraw=True, target='plot')
      self.parent.plotArea.setAxisLabel(labeltext=labeltext2, axis=axis, redraw=True, target='resid')

  def previewThis(self):
    # generates and displays a figure preview
    filename = WORKINGDIR + PATH_SEPARATOR + 'temp_fit-o-mat_preview.png'
    
    # save main graphics
    # obtain target dimensions
    targetwidth = float(self.exportSizeX.text())
    targetheight = float(self.exportSizeY.text())
    # obtain current dimensions
    currwidth, currheight = self.parent.plotArea.matplot.get_size_inches()
    
    # set new dimensions and save
    self.parent.plotArea.matplot.set_size_inches(targetwidth, targetheight)
    try:
      self.parent.plotArea.matplot.savefig(filename, format = 'png', dpi = 150, facecolor = self.parent.plotArea.figureColor)#, bbox_inches='tight')
    except:
      # some kind of error occurred
        self.parent.statusbar.showMessage('Cannot save file '+filename, self.parent.STATUS_TIME)
      
    # revert to old dimensions
    self.parent.plotArea.matplot.set_size_inches(currwidth, currheight)
      
    # issue plot redraws b/c for some reason display vanishes
    self.parent.plotArea.dataplotwidget.myRefresh()
    
    # now open a new window to display the preview image
    if(not (hasattr(self.parent, 'previewWindow'))):
      self.parent.previewWindow = QtWidgets.QMainWindow()
      self.parent.previewWindow.setWindowTitle('Preview')
  
      self.centralwidget = QWidgetMac(self.parent.previewWindow)
      self.centralwidget.setMinimumSize(QtCore.QSize(scaledDPI(320), scaledDPI(240)))
      self.parent.previewWindow.setCentralWidget(self.centralwidget)
      
      self.vLayout = QtWidgets.QVBoxLayout(self.centralwidget)
      self.vLayout.setAlignment(QtCore.Qt.AlignLeft|QtCore.Qt.AlignTop)
      self.vLayout.setContentsMargins(*[scaledDPI(2)]*4)
      
      # export button
      self.clipboardButton = QPushButtonMac()
      self.clipboardButton.setText('Copy to Clipboard')
      self.clipboardButton.setMaximumSize(QtCore.QSize(scaledDPI(150), scaledDPI(BASE_SIZE)))
      self.clipboardButton.setMinimumSize(QtCore.QSize(scaledDPI(150), scaledDPI(BASE_SIZE)))
      self.clipboardButton.clicked.connect(self.copyImageClipboard)
      self.vLayout.addWidget(self.clipboardButton)

      # generate QLabel for display
      self.displayPreview = QtWidgets.QLabel()
      self.vLayout.addWidget(self.displayPreview)
      
    # update picture
    self.displayPicture = QtGui.QPixmap(filename)
    self.displayPreview.setPixmap(self.displayPicture)
    self.displayPreview.resize(self.displayPicture.width(), self.displayPicture.height())
    # explicitly update windows size
    self.parent.previewWindow.setFixedSize(self.vLayout.sizeHint())
    
    # apply styles and show
    if(QSTYLE != None):
      self.parent.previewWindow.setStyle(QSTYLE)
    if(QSTYLESHEET != None):
      self.parent.previewWindow.setStyleSheet(QSTYLESHEET)
    self.parent.previewWindow.show()
    self.parent.previewWindow.activateWindow()

  def copyImageClipboard(self):
    # copies preview image to clipboard
    if(hasattr(self, 'displayPicture')):
      image = self.displayPicture.toImage()
      QtWidgets.QApplication.clipboard().setImage(image)   

  def exportThis(self):
    global REMEMBERDIR
    # exports current figure and residuals
    filter_options = ['PDF files (*.pdf)', 'Scalable vector graphic (*.svg)', 'Postscript (*.ps)', 'PNG image (*.png)', 'Python script (*.py)', 'All files (*.*)']
    format_options = ['pdf', 'svg', 'ps', 'png', 'py', 'pdf']
    filterstring = ';;'.join(filter_options)
    # get save file name
    filename, filter_ = QtWidgets.QFileDialog.getSaveFileName(self, filter = filterstring, directory = REMEMBERDIR, caption='Export Graphics')
    filename = str(filename)
    if(PATH_SEPARATOR in filename):
      REMEMBERDIR = filename.split(PATH_SEPARATOR)[:-1]
      REMEMBERDIR = PATH_SEPARATOR.join(REMEMBERDIR)
    elif('/' in filename):
      REMEMBERDIR = filename.split('/')[:-1]
      REMEMBERDIR = PATH_SEPARATOR.join(REMEMBERDIR)
    
    # evaluate file format
    if(filter_ in filter_options):
      index = filter_options.index(filter_)
      format_ = format_options[index]
    else:
      # use PDF as default
      format_ = 'pdf'
    
    # check whether save as Python script selected
    if(format_ != 'py'):
      # save main graphics
      # obtain target dimensions
      targetwidth = float(self.exportSizeX.text())
      targetheight = float(self.exportSizeY.text())
      # obtain current dimensions
      currwidth, currheight = self.parent.plotArea.matplot.get_size_inches()
      
      # set new dimensions and save
      self.parent.plotArea.matplot.set_size_inches(targetwidth, targetheight)
      try:
        self.parent.plotArea.matplot.savefig(filename, format = format_, dpi = 600, facecolor = self.parent.plotArea.figureColor)#, bbox_inches='tight')
      except:
        # some kind of error occurred
        self.parent.statusbar.showMessage('Cannot save file '+filename, self.parent.STATUS_TIME)
      
      # revert to old dimensions
      self.parent.plotArea.matplot.set_size_inches(currwidth, currheight)
      
      # save resid graphics
      if('.' in filename):
        filename_split = filename.split('.')
        filename = '.'.join(filename_split[:-1])
        filename += '_resid.' + filename_split[-1]
      else:
        filename += '_resid'
      # obtain target dimensions
      targetwidth = float(self.exportSizeX.text())
      targetheight = float(self.exportSizeY.text())/4.0
      # obtain current dimensions
      currwidth, currheight = self.parent.plotArea.residplot.get_size_inches()
      
      # set new dimensions and save
      self.parent.plotArea.residplot.set_size_inches(targetwidth, targetheight)
      try:
        self.parent.plotArea.residplot.savefig(filename, format = format_, dpi = 600, facecolor = self.parent.plotArea.figureColor)
      except:
        # some kind of error occurred
        self.parent.statusbar.showMessage('Cannot save file '+filename, self.parent.STATUS_TIME)
      
      # revert to old dimensions
      self.parent.plotArea.residplot.set_size_inches(currwidth, currheight)
      
      # issue plot redraws b/c for some reason display vanishes
      self.parent.plotArea.dataplotwidget.myRefresh()
      self.parent.plotArea.residplotwidget.myRefresh()
    else:
      # save graphics as Python script
      pythonOutput = '##############################################\n# plot script generated by Fit-o-mat         #'
      pythonOutput += '# version ' + VERSION + '                              #'
      pythonOutput += '''# by A.M. (andreas.moeglich@uni-bayreuth.de) #
##############################################

# initialization
import matplotlib      
import matplotlib.pyplot as plt
from matplotlib import patheffects as PathEffects
import numpy as np
from numpy import abs, arccos, arcsin, arctan, exp, cos, cosh, log, log2, log10, power, sin, sinh, sqrt, tan, tanh

# create figures for data/curves and residuals
plt.ioff()
matplot = plt.figure()
residplot = plt.figure()

'''
      # apply xkcd and pathEffects up front
      settings = self.parent.plotArea.rememberSetting
      for entry in ['xkcd', 'pathEffects']:
       if entry in settings:
         pythonOutput += settings[entry]
         
      pythonOutput += '''
ax = matplot.add_subplot(111)
ax_resid = residplot.add_subplot(111)

curves = []
dataset = []
extras = []

# set axes scale
'''
      # set linear/log on axes
      pythonOutput += 'ax.set_xscale(' + repr(self.parent.plotArea.modeX) + ')\n'
      pythonOutput += 'ax.set_yscale(' + repr(self.parent.plotArea.modeY) + ')\n'
      pythonOutput += 'ax_resid.set_xscale(' + repr(self.parent.plotArea.modeX) + ')\n'
      pythonOutput += 'ax_resid.set_yscale(\'linear\')'

      # cycle over all extras
      for index in range(len(self.parent.extras)):
        # generate curve
        pythonOutput += '\n\n###############\n'
        pythonOutput += '# extra no. ' + str(index) + ' #\n'
        pythonOutput += '###############\n'
        
        # obtain settings
        settings = self.parent.extras[index].rememberSetting
        
        # plot and format extra
        if('origin' in settings):
          pythonOutput += 'extras.append({})\n'
          if(settings['origin'].startswith('plot')):
            pythonOutput += 'extras[-1][\'handle\'], = ax.' + settings['origin'] + '\n'
          else:
            pythonOutput += 'extras[-1][\'handle\'] = ax.' + settings['origin'] + '\n'
            
          # apply styles to extra
          for entry in settings:
            if(entry != 'origin'):
              pythonOutput += 'extras[-1][\'handle\'].' + settings[entry] + '\n'

      # cycle over all curves
      for index in range(len(self.parent.fit)):
        # generate curve
        pythonOutput += '\n\n###############\n'
        pythonOutput += '# curve no. ' + str(index) + ' #\n'
        pythonOutput += '###############\n'
        data = self.parent.fit[index].reportState()

        # write function
        param = data['paramAll']
        pythonOutput += '# define function\n'
        pythonOutput += 'def ffunc_' + str(index) + '(x, ' + ', '.join(data['paramNames']) + '):\n'
        pythonOutput += '\t' + '\n\t'.join(data['ffuncstr_base'].split('\n'))
        pythonOutput += '\n\treturn y\n\n'

        # write curve data
        pythonOutput += '# curve data\n'
        pythonOutput += 'curves.append({})\n'
        pythonOutput += 'curves[-1][\'x\'] = np.array(' + self.wrapString(repr(data['x'])) + ')\n\n'
        
        # plot and format function
        pythonOutput += '# plot and format curve\n'
        param = data['paramAll']
        pythonOutput += 'param_' + str(index) + ' = ' + repr(param) + '\n'
        
        # plot curve
        pythonOutput += 'curves[-1][\'handle\'], = ax.plot(curves[-1][\'x\'], ffunc_' + str(index)
        if(len(param)):
          pythonOutput += '(curves[-1][\'x\'], *param_' + str(index) + '))\n'
        else:
          pythonOutput += '(curves[-1][\'x\']))\n'
          
        # apply styles to curve
        settings = self.parent.fit[index].rememberSetting
        for entry in settings:
          pythonOutput += 'curves[-1][\'handle\'].' + settings[entry] + '\n'
          
      # cycle over all data sets
      for index in range(len(self.parent.data)):
        # generate data set
        pythonOutput += '\n\n##############\n'
        pythonOutput += '# data no. ' + str(index) + ' #\n'
        pythonOutput += '##############\n'
        data = self.parent.data[index].reportState()

        # write plot data
        pythonOutput += 'dataset.append({})\n'
        for entry in ['x', 'y', 'yerr', 'resid']:
          if(entry in data):
            pythonOutput += 'dataset[-1][' + repr(entry) + '] = np.array(' + self.wrapString(repr(data[entry])) + ')\n\n'
        
        # plot and format function
        if(('x' in data) and ('y' in data)):
          pythonOutput += '# plot and format line/scatter graphics\n'
          pythonOutput += 'dataset[-1][\'handle\'], = ax.plot(dataset[-1][\'x\'], dataset[-1][\'y\'])\n'
          # apply styles to data set
          settings = self.parent.data[index].rememberSetting
          for entry in settings:
            pythonOutput += 'dataset[-1][\'handle\'].' + settings[entry] + '\n'
          
          # check for presence of bar plot
          if(self.parent.data[index].handleBar != None):
            pythonOutput += '\n# plot and format bar graphics\n'
            offset = self.parent.data[index].Barstyle['offset']
            pythonOutput += 'offset = ' + repr(offset) + '\n'
            useWidth = self.parent.data[index].Barstyle['width']
            pythonOutput += 'dataset[-1][\'handleBar\'] = ax.bar(dataset[-1][\'x\'] + offset, dataset[-1][\'y\'], width=' + repr(useWidth) +')\n'
            # apply styles to bar graphics
            settings = self.parent.data[index].rememberSettingBar
            if(len(settings.keys())):
              pythonOutput += 'for entry in dataset[-1][\'handleBar\']:\n'
            for entry in settings:
              pythonOutput += '\tentry.' + settings[entry] + '\n'
          else:
            pythonOutput += 'offset = 0.0\n'
          
          # check for presence of error
          if(('yerr' in data) and (self.parent.data[index].handleErr != None)):
            pythonOutput += '\n# plot and format error bars\n'
            pythonOutput += 'dataset[-1][\'handleErr\'] = ax.errorbar(dataset[-1][\'x\'] + offset, dataset[-1][\'y\'], yerr=dataset[-1][\'yerr\'], capsize=1)\n'
            # apply styles to error bars
            pythonOutput += 'dataset[-1][\'handleErr\'][0].set_linewidth(0)\n'
            pythonOutput += 'dataset[-1][\'handleErr\'][0].set_markersize(0)\n'
            settings = self.parent.data[index].rememberSettingError
            if(len(self.parent.data[index].handleErr[1])):
              pythonOutput += 'for entry in dataset[-1][\'handleErr\'][1]:\n'
              for entry in settings:
                if(hasattr(self.parent.data[index].handleErr[1][0], 'set_' + entry)):
                  pythonOutput += '\tentry.' + settings[entry] + '\n'
            if(len(self.parent.data[index].handleErr[2])):
              pythonOutput += 'for entry in dataset[-1][\'handleErr\'][2]:\n'
              for entry in settings:
                if(hasattr(self.parent.data[index].handleErr[2][0], 'set_' + entry)):
                  pythonOutput += '\tentry.' + settings[entry] + '\n'

          # check for presence of stack plot
          if(self.parent.data[index].handleStack != None):
            pythonOutput += '\n# plot and format stackplot graphics\n'
            pythonOutput += 'dataset[-1][\'handleStack\'], = ax.stackplot(dataset[-1][\'x\'], dataset[-1][\'y\'])\n'
            # apply styles to bar graphics
            settings = self.parent.data[index].rememberSettingStack
            for entry in settings:
              pythonOutput += 'dataset[-1][\'handleStack\'].' + settings[entry] + '\n'
          
          # check for presence of residuals
          if(('resid' in data) and (len(data['resid']) == len(data['x']))):
            pythonOutput += '\n# plot and format line/scatter graphics of residuals\n'
            pythonOutput += 'dataset[-1][\'handleResid\'], = ax_resid.plot(dataset[-1][\'x\'], dataset[-1][\'resid\'])\n'
            # apply styles to bar graphics
            settings = self.parent.data[index].rememberSettingResid
            for entry in settings:
              pythonOutput += 'dataset[-1][\'handleResid\'].' + settings[entry] + '\n'

      # draw residline zero
      settings = self.parent.plotArea.rememberSettingResidLine
      if('init' in settings):
        pythonOutput += '\n# plot and format zero line of residuals\n'
        pythonOutput += 'handleResidLine, = ' + settings['init'] + '\n'
        for entry in settings:
          if(entry != 'init'):
            pythonOutput += 'handleResidLine.' + settings[entry] + '\n'

      # apply plot settings
      pythonOutput += '\n\n###########################\n'
      pythonOutput += '# general plot formatting #\n'
      pythonOutput += '###########################\n'
      pythonOutput += 'ax.grid(b=True)\nax_resid.grid(b=True)\n'
      settings = self.parent.plotArea.rememberSetting
      for entry in sorted(settings.keys()):
        if(not entry in ['xkcd', 'PathEffects']):
          pythonOutput += settings[entry]# + '\n'

      # set axes limits
      pythonOutput += 'ax.set_xlim([' + repr(self.parent.plotArea.minX) + ', ' + repr(self.parent.plotArea.maxX) + '])\n'
      pythonOutput += 'ax.set_ylim([' + repr(self.parent.plotArea.minY) + ', ' + repr(self.parent.plotArea.maxY) + '])\n'
      pythonOutput += 'ax_resid.set_xlim([' + repr(self.parent.plotArea.minX) + ', ' + repr(self.parent.plotArea.maxX) + '])\n'
      pythonOutput += 'ax_resid.set_ylim([' + repr(self.parent.plotArea.minResidY) + ', ' + repr(self.parent.plotArea.maxResidY) + '])\n'

      # set window size
      targetwidth = float(self.exportSizeX.text())
      targetheight = float(self.exportSizeY.text())
      pythonOutput += 'matplot.set_size_inches('+ repr(targetwidth) + ', ' + repr(targetheight) +')\n'
      pythonOutput += 'residplot.set_size_inches('+ repr(targetwidth) + ', ' + repr(targetheight / 4.0) +')\n'

      # plot the data and show
      pythonOutput += '\n\n##########################\n'
      pythonOutput += '# draw and display plots #\n'
      pythonOutput += '##########################\n'
      pythonOutput += 'plt.draw()\nplt.show()\n'
      
      # save output to file
      try:
        writehandle = open(filename, 'w', encoding='utf-8')
        writehandle.write(pythonOutput)
        writehandle.close()
      except:
        self.parent.statusbar.showMessage('Error writing file ' + filename, self.parent.STATUS_TIME)
  
  def wrapString(self, string, limit=80, breakat=',', delimiter='\n\t'):
    # wraps long string into several lines
    outstring = ''
    while(len(string)):
      if((len(string) <= limit) or (string[limit:].find(breakat) == -1)):
        outstring += string
        string = ''
      else:
        breakposition = limit + string[limit:].find(breakat)
        outstring += string[:breakposition + 1] + delimiter
        string = string[breakposition + 1:]
    return outstring

class myCentralWidget(QWidgetMac):
  def __init__(self, argument=None, parent=None):
    super(myCentralWidget, self).__init__(argument)
    self.parent = parent

  def resizeEvent(self, event):
    # custom resize event
    self.parent.plotArea.destructAboutLogo()
    QWidgetMac.resizeEvent(self, event)
    
class myQMessageBox(QtWidgets.QMessageBox):
  def __init__(self, argument=None, parent=None):
    super(myQMessageBox, self).__init__(argument)
    self.parent = parent
    # add checkbox
    self.discardCheckBox = QtWidgets.QCheckBox('Do not ask again')
    self.setCheckBox(self.discardCheckBox)

  def exec_(self, *args, **kwargs):
    # override exec_ to return additional argument
    return QtWidgets.QMessageBox.exec_(self, *args, **kwargs), not self.discardCheckBox.isChecked()

class Ui_MainWindow(object):
  def setupUi(self, MainWindow):
    # set up z-order counter
    self.zcount = 0
    # upshift all draw items in zo to ensure display in front of axes and gridlines
    self.zOffset = 3
    # default duration for status messages
    self.STATUS_TIME = 10000
    # set up data and fit objects
    self.fit = []
    self.fit.append(FitObject(self))
    self.data = []
    self.data.append(DataObject(self))
    self.extras = []
    self.activeData = 0
    self.activeFit = 0
    self.discardCheck = True
    self.discard = False
    
    # get font list
    self.fontList = matplotlib.font_manager.fontManager.ttflist
    self.fontNames = [i.name for i in self.fontList]
    self.fontNames= sorted(list(set(self.fontNames)))
    
    # set up GUI
    self.buildRessource(MainWindow)
    
    # print Fit-o-mat information (set counter to 2 to counteract initial widget resize)
    self.plotArea.drawAboutLogo(aspect=0.95, destructCounter=2)

    # set central widget
    MainWindow.setCentralWidget(self.centralwidget)
    
  def buildRessource(self, MainWindow):
    # build the gui
    MainWindow.setObjectName("MainWindow")
    MainWindow.resize(scaledDPI(1024), scaledDPI(768))
    MainWindow.setMinimumWidth(scaledDPI(800))
    MainWindow.setMinimumHeight(scaledDPI(600))
    MainWindow.setWindowTitle('Fit-o-mat (version ' + VERSION + ')')
    self.centralwidget = myCentralWidget(argument=MainWindow, parent=self)
    self.centralwidget.setObjectName("centralwidget")
    self.vLayout0 = QtWidgets.QVBoxLayout(self.centralwidget)
    self.vLayout0.setAlignment(QtCore.Qt.AlignLeft|QtCore.Qt.AlignTop)
    self.vLayout0.setContentsMargins(0, 0, 0, 0)
    self.masterwidget = QWidgetMac()
    self.vLayout0.addWidget(self.masterwidget)
    self.hLayout = QtWidgets.QHBoxLayout(self.masterwidget)
    self.hLayout.setContentsMargins(0, 0, 0, 0)
    self.tabWidget = QtWidgets.QTabWidget()
    self.hLayout.addWidget(self.tabWidget)
    self.tabWidget.setEnabled(True)
    self.tabWidget.setGeometry(QtCore.QRect(0, 0, scaledDPI(410), scaledDPI(500)))
    self.tabWidget.setMaximumSize(QtCore.QSize(scaledDPI(410), 16777215))
    self.tabWidget.setMinimumSize(QtCore.QSize(scaledDPI(410), scaledDPI(500)))
    self.tabWidget.setObjectName("tabWidget")

    # the matplotlib canvas
    self.plotArea = MatplotlibCanvas(self)
    self.hLayout.addWidget(self.plotArea)

    # the data tab
    self.tab = QWidgetMac()
    self.tab.setObjectName("tab")
    self.vLayout = QtWidgets.QVBoxLayout(self.tab)
    self.vLayout.setContentsMargins(2, 2, 2, 2)
    self.dataarea = DataArea(self)
    self.vLayout.addWidget(self.dataarea)
    self.tabWidget.addTab(self.tab, "")
    self.tabWidget.setTabText(self.tabWidget.indexOf(self.tab), "Data")

    # the fit tab
    self.tab_2 = QWidgetMac()
    self.tab_2.setObjectName("tab_2")
    self.hLayout2 = QtWidgets.QHBoxLayout(self.tab_2)
    self.hLayout2.setContentsMargins(2, 2, 2, 2)
    self.fitarea = FitArea(self)
    self.hLayout2.addWidget(self.fitarea)
    self.tabWidget.addTab(self.tab_2, "")
    self.tabWidget.setTabText(self.tabWidget.indexOf(self.tab_2), "Fit")

    # the results tab
    self.tab_3 = QWidgetMac()
    self.tab_3.setObjectName("tab_3")
    self.hLayout3 = QtWidgets.QHBoxLayout(self.tab_3)
    self.hLayout3.setContentsMargins(2, 2, 2, 2)
    self.resultsarea = ResultsArea(self)
    self.hLayout3.addWidget(self.resultsarea)
    self.tabWidget.addTab(self.tab_3, "")
    self.tabWidget.setTabText(self.tabWidget.indexOf(self.tab_3), "Results")

    # the objects tab
    self.tab_4 = QWidgetMac()
    self.tab_4.setObjectName("tab_4")
    self.hLayout4 = QtWidgets.QHBoxLayout(self.tab_4)
    self.hLayout4.setContentsMargins(2, 2, 2, 2)
    self.objectsarea = ObjectsArea(self)
    self.hLayout4.addWidget(self.objectsarea)
    self.tabWidget.addTab(self.tab_4, "")
    self.tabWidget.setTabText(self.tabWidget.indexOf(self.tab_4), "Objects")
    
    # the graphics export tab
    self.tab_5 = QWidgetMac()
    self.hLayout5 = QtWidgets.QHBoxLayout(self.tab_5)
    self.hLayout5.setContentsMargins(2, 2, 2, 2)
    self.graphicsarea = GraphicsArea(self)
    self.hLayout5.addWidget(self.graphicsarea)
    self.tabWidget.addTab(self.tab_5, "")
    self.tabWidget.setTabText(self.tabWidget.indexOf(self.tab_5), "Graphics")
    
    # check whether default style exists
    defaultStyle = 'default.style'
    try:
      loadhandle = open(WORKINGDIR + PATH_SEPARATOR + 'styles' + PATH_SEPARATOR + defaultStyle, 'r')
      red = loadhandle.readlines()
      red = ''.join(red)
      loadhandle.close()

      # apply style sheet
      self.graphicsarea.processStyleSet(operation='load', modus=red, zoffsetData=0, zoffsetCurve=0, redraw=False)
    except:
      pass
    
    self.plotArea.initLegend()

    self.statusbar = QtWidgets.QStatusBar(MainWindow)
    MainWindow.setStatusBar(self.statusbar)
    
    blah = QtWidgets.QLabel()
    blah.setText('Status OK')
    self.statusbar.addWidget(blah)

    self.loadStateButton = QPushButtonMac()
    self.loadStateButton.setText('Open State')
    self.loadStateButton.setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
    self.loadStateButton.setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
    self.loadStateButton.clicked.connect(partial(self.loadState, None))
    self.statusbar.addPermanentWidget(self.loadStateButton)

    self.saveStateButton = QPushButtonMac()
    self.saveStateButton.setText('Save State')
    self.saveStateButton.setMaximumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
    self.saveStateButton.setMinimumSize(QtCore.QSize(scaledDPI(60), scaledDPI(BASE_SIZE)))
    self.saveStateButton.clicked.connect(self.saveState)
    self.statusbar.addPermanentWidget(self.saveStateButton)

    self.aboutButton = QPushButtonMac()
    self.aboutButton.setText('About')
    self.aboutButton.setMaximumSize(QtCore.QSize(scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.aboutButton.setMinimumSize(QtCore.QSize(scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.aboutButton.clicked.connect(self.aboutInfo)
    self.statusbar.addPermanentWidget(self.aboutButton)
  
    self.helpButton = QPushButtonMac()
    self.helpButton.setText('Help')
    self.helpButton.setMaximumSize(QtCore.QSize(scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.helpButton.setMinimumSize(QtCore.QSize(scaledDPI(40), scaledDPI(BASE_SIZE)))
    self.helpButton.clicked.connect(self.showHelp)
    self.statusbar.addPermanentWidget(self.helpButton)
    
    # give focus to empty data table
    self.dataarea.tableWidget.setFocus()
  
  def loadState(self, stateFile=None):
    # store how many objects we have before the state load
    numberData, numberFit, numberExtras = len(self.data), len(self.fit), len(self.extras)
    # open specific file or select one via file dialog
    if(stateFile != None):
      filename = stateFile
      self.discardCheck = False
      self.discard = True
    else:
      global REMEMBERDIR
      # parse state file
      filename, filter_ = QtWidgets.QFileDialog.getOpenFileName(self.centralwidget, filter = 'State file (*.state)', directory = REMEMBERDIR, caption='Open State')
      filename = str(filename)
      if(PATH_SEPARATOR in filename):
        REMEMBERDIR = filename.split(PATH_SEPARATOR)[:-1]
        REMEMBERDIR = PATH_SEPARATOR.join(REMEMBERDIR)
      elif('/' in filename):
        REMEMBERDIR = filename.split('/')[:-1]
        REMEMBERDIR = PATH_SEPARATOR.join(REMEMBERDIR)

    # read file contents
    activeCategory = ''
    try:
      loadhandle=open(filename,'r', encoding='utf-8')
      settings = {}; activeCategory = ''
      red = loadhandle.readline()
    except:
      self.statusbar.showMessage('Cannot load ' + filename, self.STATUS_TIME)
    else:
      # check whether to discard old items
      if(self.discardCheck):
        msgBox = myQMessageBox()
        msgBox.setWindowTitle('Fit-o-mat')
        msgBox.setText('Discard current objects?')
        msgBox.setStandardButtons(QtWidgets.QMessageBox.Yes | QtWidgets.QMessageBox.No)
        msgBox.setDefaultButton(QtWidgets.QMessageBox.No)
        msgBox.setIcon(QtWidgets.QMessageBox.Question)
        # apply styles and show
        if(QSTYLE != None):
          msgBox.setStyle(QSTYLE)
        if(QSTYLESHEET != None):
          msgBox.setStyleSheet(QSTYLESHEET)
        reply, self.discardCheck = msgBox.exec_()
        if (reply == QtWidgets.QMessageBox.Yes):
          self.discard = True
        else:
          self.discard = False
      # parse file contents
      while (red):
        if(activeCategory == 'MESSAGE'):
          if(red.find('</MESSAGE>') == 0):
            activeCategory = ''
          else:
            red = red.strip()
            if(activeCategory in settings):
              settings[activeCategory].append(red)
        else:
          if(red.find('<') == 0):
            if(red.find('/') == 1):
              activeCategory = ''
            else:
              activeCategory = red[1:].split('>')[0]
              if(activeCategory in ['GRAPHICS', 'CANVAS', 'OBJECTS']):
                settings[activeCategory] = {}
              else:
                settings[activeCategory] = []
          elif(red.find('>>>') == 0):
            if(activeCategory != ''):
              entry = red[3:].strip()
              red = loadhandle.readline()
              red = red.strip()
              # convert string input to original data
              try:
                red = ast.literal_eval(red)
                settings[activeCategory][entry] = red
              except:
                self.statusbar.showMessage('Failed to restore setting ' + repr(entry) + repr(red), self.STATUS_TIME)
                print('Failed to restore setting', entry, red)
          else:
            red = red.strip()
            if(activeCategory in settings):
              settings[activeCategory].append(red)
        red = loadhandle.readline()
        
      loadhandle.close()
    
      # apply settings
      # apply axes mode to avoid problems with log axes
      temp_settings = {}
      for entry in ['modeX', 'modeY']:
        if(('CANVAS' in settings) and (entry in settings['CANVAS'])):
          temp_settings[entry] = settings['CANVAS'][entry]
        else:
          temp_settings[entry] = 'linear'
      self.plotArea.restoreState(temp_settings)

      # count data sets and curves already present
      zoffsetData = len(self.data)
      zoffsetCurve = len(self.fit)
      zoffsetResid = zoffsetData
      zoffset = zoffsetData + zoffsetCurve
  
      # data sets
      datasets = [i for i in settings if i.startswith('DATA')]
      datasets = sorted(datasets, key=lambda k: k.split('_')[-1])
      if(len(datasets)):
        for entry in datasets:
          data = ''.join(settings[entry])
          try:
            data = ast.literal_eval(data)
            # need to restore 'inf' as they did not correctly propagate through ast.literal_eval
            for key in data:
              if(type(data[key]) == list):
                data[key] = [np.inf if (i == 'np.inf') else i for i in data[key]]
            # generate new data set
            self.data.append(DataObject(self))
            # and restore values
            self.data[-1].restoreState(data, zoffset, zoffsetResid)
            # cause data to be drawn
            self.data[-1].drawMe(redraw=False)
            # also create a new resid object
            self.data[-1].drawMeResid(redraw=False)
          except:
            self.statusbar.showMessage('Failed to restore data set!', self.STATUS_TIME)
            print('Failed to restore data set', data)
          
      # curve sets
      curvesets = [i for i in settings if i.startswith('CURVE')]
      curvesets = sorted(curvesets, key=lambda k: k.split('_')[-1])
      if(len(curvesets)):
        for entry in curvesets:
          data = ''.join(settings[entry])
          try:
            data = ast.literal_eval(data)
            # need to restore 'inf' as they did not correctly propagate through ast.literal_eval
            for key in data:
              if(type(data[key]) == list):
                data[key] = [np.inf if (i == 'np.inf') else i for i in data[key]]
            # generate new data set
            self.fit.append(FitObject(self))
            # and restore values
            self.fit[-1].restoreState(data, zoffset)
            # cause data to be drawn
            self.fit[-1].drawMe(redraw=False)
          except:
            self.statusbar.showMessage('Failed to restore curve!', self.STATUS_TIME)
            print('Failed to restore curve', data)
      
      # extras!
      extras = [i for i in settings if i.startswith('EXTRAS')]
      extras = sorted(extras, key=lambda k: k.split('_')[-1])
      if(len(extras)):
        for entry in extras:
          data = ''.join(settings[entry])
          try:
            data = ast.literal_eval(data)
            # generate new data set
            self.extras.append(ExtrasObject(self))
            # and restore values
            self.extras[-1].restoreState(data, zoffset)
            # cause data to be drawn
            self.extras[-1].drawMe(redraw=False)
          except:
            self.statusbar.showMessage('Failed to restore extra object!', self.STATUS_TIME)
            print('Failed to restore extra object', data)
      
      if((len(datasets)) or (len(curvesets))):
        # update legend
        self.objectsarea.updateLegend(redraw=False)
        
      # objects tab
      if('OBJECTS' in settings):
        self.objectsarea.restoreState(settings['OBJECTS'], zoffsetData, zoffsetCurve)
      
      # data area tab
      if('IMPORTTABLE' in settings):
        self.dataarea.restoreState(settings['IMPORTTABLE'])
      
      # apply canvas and graphics last to counteract autozoom when generating data and fits
      if('GRAPHICS' in settings):
        red = ''
        for key in settings['GRAPHICS']:
          red += '>>>' + key + '\n'
          red += repr(settings['GRAPHICS'][key]) + '\n'
        self.graphicsarea.processStyleSet(operation='load', modus=red, zoffsetData=zoffsetData,\
                                          zoffsetCurve=zoffsetCurve, redraw=False)

      # very finally check whether state file contained a message to display
      if('MESSAGE' in settings):
        self.displayMessage(settings['MESSAGE'])
      
      # delete initial data and curve objects
      if(self.discard):
        # delete surplus fit objects
        numberFit = min(numberFit, len(self.fit) - 1)
        for entry in range(numberFit)[::-1]:
          self.objectsarea.deleteCurve(entry, redraw=False)
        # delete surplus data objects
        numberData = min(numberData, len(self.data) - 1)
        for entry in range(numberData)[::-1]:
          self.objectsarea.deleteDataSet(entry, redraw=False)
        # delete surplus extra objects
        for entry in range(numberExtras)[::-1]:
          self.objectsarea.deleteExtra(entry, redraw=False)

      # canvas comes last to preserve axis settings
      if('CANVAS' in settings):
        self.plotArea.restoreState(settings['CANVAS'])
        
      # restore discardCheck when loading state on startup
      if(stateFile != None):
        self.discardCheck = True
        self.discard = False
        
      # finally refresh plots
      self.plotArea.dataplotwidget.myRefresh()
      self.plotArea.residplotwidget.myRefresh()

  def saveState(self):
    global REMEMBERDIR
    # exports current settings and data
    filter_options = ['State file (*.state)', 'All files (*.*)']
    filterstring = ';;'.join(filter_options)
    # get save file name
    filename, filter_ = QtWidgets.QFileDialog.getSaveFileName(self.centralwidget, filter = filterstring, directory=REMEMBERDIR, caption='Save State')
    filename = str(filename)
    if(PATH_SEPARATOR in filename):
      REMEMBERDIR = filename.split(PATH_SEPARATOR)[:-1]
      REMEMBERDIR = PATH_SEPARATOR.join(REMEMBERDIR)
    elif('/' in filename):
      REMEMBERDIR = filename.split('/')[:-1]
      REMEMBERDIR = PATH_SEPARATOR.join(REMEMBERDIR)
    
    # prepare file output
    try:
      writehandle = open(filename, 'w', encoding='utf-8')
      
      # process canvas
      writehandle.write('<CANVAS>\n')
    except:
      self.statusbar.showMessage('Cannot save ' + filename, self.STATUS_TIME)
    else:
      settings = self.plotArea.reportState()
      for key in settings:
        red = '>>>' + key + '\n' + repr(settings[key]) + '\n'
        writehandle.write(red)
      writehandle.write('</CANVAS>\n')
      
      # process objects tab
      writehandle.write('\n<OBJECTS>\n')
      objects = self.objectsarea.reportState()
      writehandle.write(objects)
      writehandle.write('</OBJECTS>\n')
      
      # process graphics tab
      writehandle.write('\n<GRAPHICS>\n')
      settings = self.graphicsarea.processStyleSet(operation='save', modus='string')
      writehandle.write(settings)
      writehandle.write('</GRAPHICS>\n')
      
      # process data area
      writehandle.write('\n<IMPORTTABLE>\n')
      dataTable = self.dataarea.reportState()
      writehandle.write(repr(dataTable) + '\n')
      writehandle.write('</IMPORTTABLE>\n')
      
      # write all data and fit objects
      for index, entry in enumerate(self.data):
        writehandle.write('\n<DATA_' + str(index) + '>\n')
        data = entry.reportState()
        data = self.replaceInf(repr(data))
        writehandle.write(data + '\n')
        writehandle.write('</DATA_' + str(index) + '>\n')
  
      for index, entry in enumerate(self.fit):
        writehandle.write('\n<CURVE_' + str(index) + '>\n')
        curve = entry.reportState()
        curve = self.replaceInf(repr(curve))
        writehandle.write(curve + '\n')
        writehandle.write('</CURVE_' + str(index) + '>\n')

      # write all extra objects
      for index, entry in enumerate(self.extras):
        writehandle.write('\n<EXTRAS_' + str(index) + '>\n')
        extras = repr(entry.reportState())
        writehandle.write(extras + '\n')
        writehandle.write('</EXTRAS_' + str(index) + '>\n')
    
      writehandle.close()

  def replaceInf(self, literal):
    # function to replace any 'inf' by 'np.inf' (otherwise data cannot be loaded again)
    literal = literal.replace('inf]', '\'np.inf\']')
    literal = literal.replace('inf,', '\'np.inf\',')
    return literal
    
  def showHelp(self):
    # display help file in browser
    helpFile = WORKINGDIR + PATH_SEPARATOR + 'manual' + PATH_SEPARATOR + 'Fit-o-mat.html'
    try:
      readhandle = open(helpFile, 'r')
      readhandle.close()
    except:
      self.statusbar.showMessage('Cannot locate local copy of help files, redirecting to homepage!', self.STATUS_TIME)
      helpFile = 'http://www.moeglich.uni-bayreuth.de/en/fit-o-mat'
    webbrowser.open(helpFile)

  def aboutInfo(self):
    # display information on canvas
    self.plotArea.drawAboutLogo()

  def displayMessage(self, message=''):
    # displays message contained in state file
    if(len(message)):
      messageText = '\n'.join(message)
      # open window that displays message
      self.daughterWindow = QtWidgets.QMainWindow()
      self.daughterWindow.setWindowTitle('Message Window')
      
      self.centralwidget = QWidgetMac(self.daughterWindow)
      self.centralwidget.setMinimumSize(QtCore.QSize(scaledDPI(320), scaledDPI(240)))
      self.daughterWindow.setCentralWidget(self.centralwidget)
      
      self.vLayout = QtWidgets.QVBoxLayout(self.centralwidget)
      self.vLayout.setAlignment(QtCore.Qt.AlignCenter|QtCore.Qt.AlignTop)
      self.vLayout.setContentsMargins(0, 0, 0, 0)

      self.messageField = QtWidgets.QTextBrowser()
      self.messageField.setOpenExternalLinks(True)
      self.messageField.setGeometry(QtCore.QRect(0, 0, scaledDPI(500), scaledDPI(600)))
      self.vLayout.addWidget(self.messageField)
      self.messageField.setReadOnly(True)
      self.messageField.setHtml(messageText)
      
      # apply styles and show
      if(QSTYLE != None):
        self.daughterWindow.setStyle(QSTYLE)
      if(QSTYLESHEET != None):
        self.daughterWindow.setStyleSheet(QSTYLESHEET)
      self.daughterWindow.show()
    
  def formatNumber(self, number):
    # formats number for output
    NUMBER_SWITCH = 1e3
    FORMAT_DECIMAL = '{:.4f}'
    FORMAT_SCIENTIFIC = '{:.4e}'
    # determine return string
    if((self.isNumber(number)) and (np.isfinite(float(number)))):
      if((np.abs(number)>NUMBER_SWITCH) or (np.abs(number)<1.0/NUMBER_SWITCH)):
        numberstr = FORMAT_SCIENTIFIC.format(number)
      else:
        numberstr = FORMAT_DECIMAL.format(number)
    else:
      numberstr = str(number)
    
    return numberstr

  def isNumber(self, s):
    # checks whether string is a number
    try:
      float(s)
      return True
    except ValueError:
      pass
   
    try:
      import unicodedata
      unicodedata.numeric(s)
      return True
    except (TypeError, ValueError):
      pass
    
    return False


class MyForm(QtWidgets.QMainWindow):
  def __init__(self, parent=None):
    QtWidgets.QWidget.__init__(self, parent)
    # adjust DPI scaling
    global DPI_SCALING
    self.targetDPI = 96
    actualDPI = QtGui.QPaintDevice.logicalDpiX(self)
    DPI_SCALING = 1.0 * actualDPI / self.targetDPI
    self.ui = Ui_MainWindow()
    self.ui.setupUi(MainWindow=self)

  def closeEvent(self, event):
    msgBox = QtWidgets.QMessageBox()
    msgBox.setWindowTitle('Fit-o-mat')
    msgBox.setText('Close program?')
    msgBox.setStandardButtons(QtWidgets.QMessageBox.Yes | QtWidgets.QMessageBox.No)
    msgBox.setDefaultButton(QtWidgets.QMessageBox.Yes)
    msgBox.setIcon(QtWidgets.QMessageBox.Question)
    # apply styles and show
    if(QSTYLE != None):
      msgBox.setStyle(QSTYLE)
    if(QSTYLESHEET != None):
      msgBox.setStyleSheet(QSTYLESHEET)
    reply = msgBox.exec_()
    if (reply == QtWidgets.QMessageBox.Yes):
      # check whether message window exists and close it
      if(hasattr(self.ui, 'daughterWindow')):
        self.ui.daughterWindow.close()
      # check whether preview window exists and close it
      if(hasattr(self.ui, 'previewWindow')):
        self.ui.previewWindow.close()
      event.accept()
    else:
      event.ignore()

  def keyPressEvent(self, event):
    if event.matches(QtGui.QKeySequence.Save):
      # trigger save state on CTRL-S
      self.ui.saveState()
    elif event.matches(QtGui.QKeySequence.Open):
      # trigger load state on CTRL-O
      self.ui.loadState()
    elif event.matches(QtGui.QKeySequence.HelpContents):
      # trigger help
      self.ui.showHelp()
    elif event.matches(QtGui.QKeySequence.Print):
      # export graphics on CTRL-P
      self.ui.graphicsarea.exportThis()
    elif event.matches(QtGui.QKeySequence.Quit):
      # close program on CTRL-Q
      self.ui.close()
    
def scaledDPI(size):
  # adjusts GUI dimensions to correct for DPI
  # implement check for array
  return int(size * DPI_SCALING)

if __name__ ==  "__main__":
  # are we on win or linux platform?
  if((sys.platform == 'linux') or (sys.platform == 'darwin')):
    PATH_SEPARATOR = '/'
  else:
    PATH_SEPARATOR = '\\'
    
  # determine working directors
  if((len(sys.path)) and (len(sys.path[0]))):
    WORKINGDIR = sys.path[0]
  else:
    WORKINGDIR = '.'
  HOMEDIR = expanduser('~')
  REMEMBERDIR = HOMEDIR
    
  # start app
  DPI_SCALING = 1.0
  QSTYLE, QSTYLESHEET = None, None
  if(sys.platform == 'darwin'):
    # special treatment for OS X (native style is just killing me)
    BASE_SIZE = 22
    QSTYLE = QtWidgets.QStyleFactory.create('Fusion')
    # set style sheet to approx. retain correct look
    QSTYLESHEET  = "QComboBox {font-size: 8pt; margin: 0px; padding-left: 3px;}\n\
                    QWidget {font-size: 8pt; margin: 0px; padding: 0px;}\n\
                    QRadioButton {font-size: 8pt; margin: 0px; padding: 0px; spacing: 3px;}\n\
                    QRadioButton::indicator {width: 12px; height: 12px;}\n\
                    QTableView::item:focus {background-color: white; color: black;}\n\
                    QGroupBox {font-size: 8pt; margin: 0px; border-style: inset; border-width: 1px; border-radius: 3px; border-color: #777777;}\n\
                    QCheckBox {font-size: 8pt; margin: 0px; padding: 0px; spacing: 3px;}\n"
  else:
    BASE_SIZE = 22
    QSTYLE = QtWidgets.QStyleFactory.create('Fusion')
    QSTYLESHEET  = "QTableView::item:focus {background-color: white; color: black;}\n\
                    QGroupBox {border-style: inset; border-width: 1px; border-radius: 3px; border-color: #777777;}\n"
                    #QWidget {margin: 0px; padding: 0px;}\n\
    if('linux' in sys.platform):
      QSTYLESHEET += "QWidget {font-size: 8pt;}\n"
  
  app = QtWidgets.QApplication(sys.argv)
  myapp = MyForm()
  if(QSTYLE != None):
    myapp.setStyle(QSTYLE)
  if(QSTYLESHEET != None):
    myapp.setStyleSheet(QSTYLESHEET)
  myapp.show()
  
  # now check whether state should be loaded
  if(len(sys.argv) > 1):
    QtCore.QCoreApplication.processEvents()
    myapp.ui.loadState(stateFile=sys.argv[1])
  
  sys.exit(app.exec_())