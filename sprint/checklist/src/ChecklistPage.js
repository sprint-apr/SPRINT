import { useEffect, useState } from 'react';
import { DataGrid } from '@mui/x-data-grid';
import { Button, Checkbox, Paper, IconButton } from '@mui/material';
import axios from 'axios';
import { useMemo } from 'react';
import Dialog from '@mui/material/Dialog';
import DialogTitle from '@mui/material/DialogTitle';
import DialogContent from '@mui/material/DialogContent';
import DialogActions from '@mui/material/DialogActions';
import CheckCircleIcon from '@mui/icons-material/CheckCircle';
import CancelIcon from '@mui/icons-material/Cancel';
import HelpOutlineIcon from '@mui/icons-material/HelpOutline';
import { Prism as SyntaxHighlighter } from 'react-syntax-highlighter';

const BACKEND_URL = "http://163.152.161.61:8000";
const COLUMNS_TO_SHOW = [
  'id',
  'bug_id',
  'correct',
  'noCorrect',
  'version',
  'file',
  'line',
  'rewritten_source',
  'dev_patch',
  'chat_repair_patch'
];

const columnWidths = {
  bug_id: 100,
  version: 100,
  correct: 100,
  noCorrect: 80,
  line: 25,
  dev_patch: 90,
  file: 400,
  rewritten_source: 400,
  chat_repair_patch: 300,
}

const fetchData = async (setLoading, setData) => {
  try {
    setLoading(true);
    const data = (await axios.get(`${BACKEND_URL}/abstract_patches`)).data;
    const bugs = (await axios.get(`${BACKEND_URL}/bugs`)).data;
    data.forEach((row) => {
      row['dev_patch'] = bugs[row['bug_id']]['dev_patch']
      row['chat_repair_patch'] = bugs[row['bug_id']]['chat_repair_patch']
    })
    setData(data.filter((row) => row.rewriting_succeed));
  } catch (error) {
    console.error('Error fetching data:', error);
  } finally {
    setLoading(false);
  }
}

export function MainPage() {
  const [data, setData] = useState([]);
  const [loading, setLoading] = useState(false);
  const [openModal, setOpenModal] = useState(false);
  const [modalContent, setModalContent] = useState({});

  const handleCorrectCheck = async (row, newValue) => {
    try {
      const response = await axios.post(`${BACKEND_URL}/abstract_patches/${row.id}`, { correct: newValue });
      if (response.status !== 200) {
        throw new Error(`Failed to update correctness for AP ${row.id}`);
      }
      setData((prevData) =>
        prevData.map((r) =>
          r.id === row.id ? { ...r, correct: newValue } : r
        )
      );
    } catch (error) {
      console.error("Error updating correct value:", error);
    }
  } 

  const handleNoCorrectCheck = async (currentRow, newValue) => {
    try {
      const response = await axios.post(`${BACKEND_URL}/abstract_patches/no_correct/${currentRow.id}`, { no_correct: newValue });
      if (response.status !== 200) {
        throw new Error(`Failed to update noCorrect for AP ${currentRow.id}`);
      }
      setData((prevData) =>
        prevData.map((r) =>
          r.bug_id === currentRow.bug_id ? response.data.find((({id}) => id === r.id)) : r
      ));
    } catch (error) {
      console.error("Error updating noCorrect value:", error);
    }
  } 

  const handlePatchClick = (row, is_dev) => {
    setModalContent({
      title: row.bug_id,
      content: is_dev ? row.dev_patch : row.chat_repair_patch,
      language: is_dev ? 'diff' : 'java',
    });
    setOpenModal(true);
  }

  useEffect(() => {
    fetchData(setLoading, setData);
  }, []);

  const rows = data;
  const columns = useMemo(() => {
    if (data.length > 0) {
      return COLUMNS_TO_SHOW
        .filter((key) => COLUMNS_TO_SHOW.includes(key))
        .map((key) => {
          let renderCell;
          if (key === 'correct') {
            renderCell = (params) => (
              <div style={{ display: 'flex', flexDirection: 'row', alignItems: 'center' }}>
                <IconButton
                  size=''
                  sx={{paddingLeft: 0, paddingRight: 0}}
                  color={params.row.correct === true ? 'error' : 'default'}
                  onClick={() => handleCorrectCheck(params.row, true)}
                >
                  <CheckCircleIcon />
                </IconButton>
                <IconButton
                  size='xs'
                  sx={{paddingLeft: 0, paddingRight: 0}}
                  color={params.row.correct === false ? 'error' : 'default'}
                  onClick={() => handleCorrectCheck(params.row, false)}
                >
                  <CancelIcon />
                </IconButton>
                <IconButton
                  size='xs'
                  sx={{paddingLeft: 0, paddingRight: 0}}
                  color={params.row.correct === null ? 'error' : 'default'}
                  onClick={() => handleCorrectCheck(params.row, null)}
                >
                  <HelpOutlineIcon />
                </IconButton>
              </div>
            );
          } else if (key === 'noCorrect') {
            renderCell = (params) => {
              const disableNoCorrect = data.some(row => row.bug_id === params.row.bug_id && row.correct);
              return (
                <Checkbox color={'error'}
                  checked={params.row.no_correct}
                  disabled={disableNoCorrect}
                  onChange={(e) => handleNoCorrectCheck(params.row, e.target.checked)}
                />
              );
            }
          } else if (key === 'dev_patch') {
            renderCell = (params) => (
              <Button onClick={() => handlePatchClick(params.row, true)}>
                <div style={{ fontSize: '0.6rem' }}>
                  Show
                </div>
              </Button>
            );
          } else if (key === 'chat_repair_patch') {
            renderCell = (params) => (
              params.value && 
              <Button onClick={() => handlePatchClick(params.row, false)}>
                <div style={{ fontSize: '0.6rem' }}>
                  Show
                </div>
              </Button>
            );
          } else if (key === 'rewritten_source') {
            renderCell = (params) => (
              <SyntaxHighlighter language="java">
                {params.value?.replaceAll('"<FL4APR_MASK>"', "□")}
              </SyntaxHighlighter>
            );
          }
          return ({
            field: key,
            headerName: key[0].toUpperCase() + key.slice(1),
            renderCell,
            width: columnWidths[key] || 200,
          });
        })
    }
    return [];
  }, [data]);

  return (
    <Paper sx={{ height: '100vh', width: '100%' }}>
      <DataGrid
        initialState={{
          sorting: {
            sortModel: [{ field: 'bug_id', sort: 'asc' }],
          },
          columns: {
            columnVisibilityModel: {
              id: false,
              version: true,
            },
          }
        }}
        rows={rows}
        columns={columns}
        loading={loading}
        sx={{ 
          border: 0,
          fontSize: '0.6rem',
          '& .unchecked-row': {
            bgcolor: 'lightyellow',
          }
        }}
        getRowClassName={(params) =>
          params.row.correct === null ? 'unchecked-row' : ''
        }
      />
      {modalContent && 
        <Dialog
          open={openModal}
          onClose={() => setOpenModal(false)}
          maxWidth="md"
          fullWidth
        >
          <DialogTitle>{`Patch Preview ${modalContent['title']}`}</DialogTitle>
          <DialogContent dividers>
            <SyntaxHighlighter language={modalContent['language']}>
              {modalContent.content}
            </SyntaxHighlighter>
          </DialogContent>
          <DialogActions>
            <Button onClick={() => setOpenModal(false)}>Close</Button>
          </DialogActions>
        </Dialog>
      }
    </Paper>
  );
}
